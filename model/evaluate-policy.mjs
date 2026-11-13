import { readFileSync } from 'node:fs';
import { createHash } from 'node:crypto';
import { assessCompletion, buildCompletionContract } from './completion.mjs';
import { createPolicySession, decidePolicy, censorPolicyAction, STRATEGY_REVIEW } from './policy-runtime.mjs';

const read = name => JSON.parse(readFileSync(new URL(name, import.meta.url), 'utf8'));
const contract = buildCompletionContract(read('./catalogue.json'), read('./completion-profile.json'));
const requirementsSha256 = createHash('sha256').update(readFileSync(new URL('./completion-requirements.json', import.meta.url))).digest('hex');
export const CHECKPOINT_SEMANTICS = 'native-action-and-timer-boundaries-v1';

/** A cheap necessary condition avoids allocating a full missing-goal report each frame. */
function completeObservation(observation) {
  if (!contract.requiredAchievements.every(({ name }) => observation.achievements?.[name] === true)) return false;
  return assessCompletion(observation, contract).complete;
}

/**
 * Execute a fixed, observation-only policy on the full pinned engine.
 * This is a finite experiment, not an optimality certificate or an exact expectation.
 * The sample-stream seed belongs to the evaluator. The native startup seed may
 * be read through Export save. Timing selected to change seeded outcomes is
 * forbidden and needs a decision-rule audit; action replay cannot certify it.
 */
export function evaluatePolicy(source, {
  horizonMs = 60_000, maxDecisions = 100_000, maxSameTimeActions = 2000,
  decisionTimeoutMs = 1000, recordObservations = false, recordAudit = true, onProgress = null, progressEveryMs = 60_000, ...environment
} = {}) {
  if (!Number.isSafeInteger(horizonMs) || horizonMs < 0
      || !Number.isSafeInteger(maxDecisions) || maxDecisions < 1
      || !Number.isSafeInteger(maxSameTimeActions) || maxSameTimeActions < 1) {
    throw new Error('Expected finite nonnegative horizon and positive decision budgets');
  }
  if (!Number.isInteger(decisionTimeoutMs) || decisionTimeoutMs < 1 || decisionTimeoutMs > 0xffffffff) {
    throw new Error('Decision timeout must be a positive uint32 integer in milliseconds');
  }
  if (onProgress !== null && typeof onProgress !== 'function' || !Number.isSafeInteger(progressEveryMs) || progressEveryMs < 1) {
    throw new Error('Progress requires a callback and a positive integer interval');
  }
  if (environment.onTransition || environment.transitionAchievementGate || environment.diagnosticMode || environment.initialize === false) {
    throw new Error('Policy experiments require unmodified initial gameplay and the built-in observer');
  }
  const records = [];
  const policySha256 = createHash('sha256').update(source).digest('hex');
  const experimentBudgets = { horizonMs, maxDecisions, maxSameTimeActions, decisionTimeoutMs };
  let firstCompletionMs = null;
  let lastCheckpointMs = 0;
  let checkpointCount = 0;
  const session = createPolicySession({ ...environment, recordAudit,
    transitionAchievementGate: recordObservations ? undefined : contract.requiredAchievements.map(({ name }) => name),
    onTransition: event => {
    if (!Number.isSafeInteger(event.elapsedMs) || event.elapsedMs < lastCheckpointMs) {
      throw new Error('Transition observer returned a nonmonotone clock');
    }
    lastCheckpointMs = event.elapsedMs;
    checkpointCount++;
    if (firstCompletionMs === null && event.observation && completeObservation(event.observation)) firstCompletionMs = event.elapsedMs;
    if (recordObservations) records.push({ kind: event.kind, elapsedMs: event.elapsedMs, observation: event.observation });
  } });
  const { policy } = session;
  let observation = policy.observe();
  let memory = null;
  let decisions = 0;
  let sameTimeActions = 0;
  let previousTime = observation.elapsedMs;
  let status = 'censored';
  let error = null;
  let decisionFailure = null;
  let nextProgressMs = progressEveryMs;
  while (firstCompletionMs === null && observation.elapsedMs <= horizonMs) {
    if (decisions >= maxDecisions || sameTimeActions >= maxSameTimeActions) { status = 'decision-limit'; break; }
    try {
      const inputs = { observation, actions: policy.actions(), memory };
      let result;
      try {
        result = decidePolicy(source, inputs.observation, inputs.actions, inputs.memory, { timeoutMs: decisionTimeoutMs });
      } catch (cause) {
        // Match decidePolicy's JSON boundary exactly. These are only its public
        // inputs, not an engine checkpoint, random state or resumable save.
        decisionFailure = {
          schemaVersion: 1, kind: 'policy-decision', policySha256,
          decisionIndex: decisions, sameTimeActions, experimentBudgets: { ...experimentBudgets },
          message: cause instanceof Error ? cause.message : String(cause),
          inputs: JSON.parse(JSON.stringify(inputs)),
        };
        throw cause;
      }
      const wrapped = result && typeof result === 'object' && Object.hasOwn(result, 'action');
      let action = wrapped ? result.action : result;
      if (wrapped) memory = result.memory ?? null;
      if (!action || typeof action !== 'object' || Array.isArray(action)) throw new Error('Policy returned no action');
      if (action.type === 'wait') {
        if (!Number.isFinite(action.milliseconds) || action.milliseconds < 0) throw new Error('Policy returned an invalid wait');
        // Censoring takes the prefix of a longer wait. It adds no intervening decision.
      }
      const remaining=horizonMs-observation.elapsedMs;
      const requestedTime=action.type==='sequence' && Array.isArray(action.actions)
        ? action.actions.reduce((sum,a)=>sum+(a?.type==='wait' ? a.milliseconds : 0),0)
        : action.type==='wait' ? action.milliseconds : 0;
      const cutInsideAction=requestedTime>remaining;
      action = censorPolicyAction(action,remaining);
      observation = policy.act(action);
      decisions++;
      if (observation.elapsedMs === previousTime) sameTimeActions++;
      else sameTimeActions = 0;
      previousTime = observation.elapsedMs;
      if (onProgress && observation.elapsedMs >= nextProgressMs) {
        const counts=session.exportSummary();
        onProgress(Object.freeze({ elapsedMs: Math.floor(observation.elapsedMs), decisions,
          cookiesEarned: observation.cookiesEarned, cookiesPs: observation.cookiesPs,
          ascensions: observation.ascensions, stage: wrapped ? result.stage ?? null : null,
          actionCount: counts.actionCount, randomDrawCount: counts.randomDrawCount, checkpointCount }));
        nextProgressMs = observation.elapsedMs + progressEveryMs;
      }
      // Include precommitted and newly chosen zero-time inputs at H. Stop only
      // when the next requested positive-time prefix would leave the horizon.
      if(cutInsideAction)break;
    } catch (cause) {
      status = 'policy-error';
      error = cause instanceof Error ? cause.message : String(cause);
      break;
    }
  }
  if (firstCompletionMs !== null) status = 'complete';
  // The audit snapshot remains available after a failed input. A precommitted
  // sequence can have a successful prefix before its later action fails.
  const { observation: finalObservation, ...audit } = session.exportSummary({ includeObservation: true });
  observation = finalObservation;
  const replay = recordAudit ? session.exportTrace() : null;
  const { randomSeed: _sampleSeed, ...sharedEnvironment } = audit.environment;
  // Recording mode is deliberately excluded: summary and full experiments
  // share transitions. Adapter revisions and JS runtimes do affect semantics.
  const environmentSha256 = createHash('sha256').update(JSON.stringify({ environment: sharedEnvironment,
    adapterSourceHashes: audit.adapterSourceHashes, executionRuntime: audit.executionRuntime })).digest('hex');
  const result = {
    schemaVersion: 1,
    policySha256,
    environmentSha256,
    profileId: contract.profileId,
    checkpointSemantics: CHECKPOINT_SEMANTICS,
    strategyReview: { ...STRATEGY_REVIEW },
    status, error, decisionFailure, firstCompletionMs,
    experimentBudgets,
    requestedHorizonMs: horizonMs, observedUntilMs: Math.floor(observation.elapsedMs),
    decisions, checkpointCount,
    completion: assessCompletion(observation, contract),
    observation,
    audit,
    replay,
  };
  if (recordObservations) result.checkpointTrace = {
    schemaVersion: 1, checkpointSemantics: CHECKPOINT_SEMANTICS, profileId: contract.profileId, requirementsSha256, records,
  };
  return result;
}

/**
 * Exact arithmetic for the empirical restricted mean: mean(min(T, horizon)).
 * Censored paths keep their full horizon cost. Failed/budget-limited experiments
 * are rejected. This sample statistic does not bound the unrestricted expectation.
 */
export function summarizeExperiments(results) {
  if (!Array.isArray(results) || results.length === 0) throw new Error('At least one experiment is required');
  const horizon = results[0].requestedHorizonMs;
  let total = 0n;
  let completed = 0;
  for (const result of results) {
    if (result.requestedHorizonMs !== horizon || result.policySha256 !== results[0].policySha256
        || result.profileId !== results[0].profileId || result.environmentSha256 !== results[0].environmentSha256) {
      throw new Error('Experiments must share policy, profile, environment, and horizon');
    }
    if (!['complete', 'censored'].includes(result.status)) throw new Error('An incomplete experiment cannot be scored as a censored full-horizon sample');
    if (result.status === 'complete') {
      if (!Number.isSafeInteger(result.firstCompletionMs) || result.firstCompletionMs < 0
          || result.firstCompletionMs > horizon) throw new Error('Invalid completion time');
      total += BigInt(result.firstCompletionMs);
      completed++;
    } else {
      if (result.firstCompletionMs !== null || result.observedUntilMs !== horizon) throw new Error('Censored sample did not observe the full horizon');
      total += BigInt(horizon);
    }
  }
  return {
    policySha256: results[0].policySha256, profileId: results[0].profileId, environmentSha256: results[0].environmentSha256,
    horizonMs: horizon, samples: results.length, completed, censored: results.length - completed,
    empiricalRestrictedMeanMilliseconds: { numerator: total.toString(), denominator: String(results.length) },
    unrestrictedExpectedCompletionTime: null,
    optimalityCertified: false,
    strategyReview: { ...STRATEGY_REVIEW },
  };
}

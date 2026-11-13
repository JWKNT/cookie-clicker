import vm from 'node:vm';
import { readFileSync } from 'node:fs';
import { createHash } from 'node:crypto';
import { createRuntime } from './runtime.mjs';
import { SOURCE_HASHES } from './game-source.mjs';

// Pin the replay/evaluation dependency closure, including the completion
// implementation and the data it reads. Generated policy code has its own hash.
// These pins are separate from the eight game files and are not a refinement proof.
export const ADAPTER_SOURCE_FILES = Object.freeze([
  'runtime.mjs', 'maintenance-schedule.mjs', 'policy-runtime.mjs', 'evaluate-policy.mjs', 'game-source.mjs', 'completion.mjs',
  'catalogue.json', 'completion-profile.json', 'completion-requirements.json',
  'mathematical-assumptions.json',
]);
export const ADAPTER_SOURCE_HASHES = Object.freeze(Object.fromEntries(
  ADAPTER_SOURCE_FILES.map(name =>
    [`model/${name}`, createHash('sha256').update(readFileSync(new URL(name, import.meta.url))).digest('hex')]),
));
export const EXECUTION_RUNTIME = Object.freeze({ node: process.version, v8: process.versions.v8,
  platform: process.platform, architecture: process.arch });
export const FIXED_HERALDS = 100;

// A replay supplies actions, not the rule that selected their timestamps.
// Export inspection is permitted; seed-targeted timing is forbidden. Neither
// the VM boundary nor a successful action replay proves the latter restriction.
export const STRATEGY_REVIEW = Object.freeze({
  strategyAdmissibilityCertified: false,
  actionReplayScope: 'implemented-controls-and-current-save-history',
  seededTimingRule: 'forbidden',
  seededTimingAudit: 'decision-rule-review-required',
});

const sameEntries = (a, b) => JSON.stringify(Object.entries(a || {}).sort()) === JSON.stringify(Object.entries(b).sort());

const copy = value => structuredClone(value);
function freeze(value) {
  if (value && typeof value === 'object') { for (const child of Object.values(value)) freeze(child); Object.freeze(value); }
  return value;
}

/** Capability-limited interface for a policy. Audit data is held by the separate session. */
export function createPolicySession(options = {}) {
  if (options.diagnosticMode || options.initialize === false) throw new Error('A policy session requires normal initialized gameplay');
  if (options.heralds !== undefined && options.heralds !== FIXED_HERALDS) {
    throw new Error('The selected completion environment requires a fixed herald count of 100');
  }
  const runtime = createRuntime({ ...options, heralds: FIXED_HERALDS,
    randomTape: options.randomTape ? [...options.randomTape] : undefined, diagnosticMode: false });
  let failure = null;
  const live = () => { if (failure) throw new Error('Policy session stopped after a failed action'); };
  const policy = Object.freeze({
    observe: () => { live(); return freeze(copy(runtime.snapshot())); },
    actions: () => { live(); return freeze(copy(runtime.actions())); },
    act: action => {
      live(); const clean = copy(action);
      try {
        // A sequence is a finite, precommitted list of ordinary inputs. It has
        // no conditions or observation capability between inputs. The replay
        // records the expanded native actions, never an extra aggregate action.
        if (clean?.type === 'sequence') {
          if (!Array.isArray(clean.actions) || clean.actions.length < 1 || clean.actions.length > 1000
            || clean.actions.some(a => !a || typeof a !== 'object' || Array.isArray(a) || a.type === 'sequence')) {
            throw new Error('A policy sequence requires 1–1000 flat native actions');
          }
          let last;
          for (let i = 0; i < clean.actions.length; i++) last = runtime.act(clean.actions[i], { observe: i === clean.actions.length - 1 });
          return freeze(copy(last));
        }
        return freeze(copy(runtime.act(clean)));
      }
      catch (error) { failure = { action: clean, message: error instanceof Error ? error.message : String(error),
        ...(error?.name === 'AdmissibilityError' ? { kind: 'inadmissible-trace', reason: error.code } : {}) }; throw error; }
    },
  });
  return Object.freeze({
    policy,
    exportSummary: ({ includeObservation = false } = {}) => freeze({
      schemaVersion: 1, gameVersion: '2.053', edition: 'steam', sourceHashes: { ...SOURCE_HASHES },
      adapterSourceHashes: { ...ADAPTER_SOURCE_HASHES }, executionRuntime: { ...EXECUTION_RUNTIME },
      strategyReview: { ...STRATEGY_REVIEW },
      environment: copy(runtime.environment), ...runtime.auditCounts(), failure: copy(failure),
      ...(includeObservation ? { observation: copy(runtime.snapshot()) } : {}),
    }),
    exportTrace: () => {
      if (runtime.auditCounts().recordingMode !== 'full') throw new Error('Summary-only recording has no full replay history; use exportSummary');
      return freeze({
      schemaVersion: 1, gameVersion: '2.053', edition: 'steam', sourceHashes: { ...SOURCE_HASHES },
      adapterSourceHashes: { ...ADAPTER_SOURCE_HASHES }, executionRuntime: { ...EXECUTION_RUNTIME },
      strategyReview: { ...STRATEGY_REVIEW },
      environment: copy(runtime.environment), ...runtime.auditCounts(), actions: copy(runtime.events), randomTape: copy(runtime.consumedRandom), failure: copy(failure),
    }); },
  });
}

/** Contains no VM, clock mutator, source, future tape, direct private-state or audit-trace capability.
 * A policy may inspect the current save only through the native export action and visible textarea. */
export const createPolicyRuntime = options => createPolicySession(options).policy;

/** Prefix of a precommitted input sequence at an elapsed-time horizon. */
export function censorPolicyAction(action, remainingMs) {
  if (action.type === 'wait') return {...action,milliseconds:Math.min(action.milliseconds,remainingMs)};
  if (action.type !== 'sequence' || !Array.isArray(action.actions)) return action;
  const actions=[];let left=remainingMs;
  for(const input of action.actions) {
    if(input?.type==='wait' && Number.isFinite(input.milliseconds) && input.milliseconds>=0) {
      if(input.milliseconds>left) { actions.push({...input,milliseconds:left});break; }
      actions.push(input);left-=input.milliseconds;
    } else actions.push(input);
  }
  return {...action,actions};
}

export function replayPolicyTrace(trace, { sourceDirectory, onTransition } = {}) {
  if (trace.schemaVersion !== 1 || trace.gameVersion !== '2.053' || trace.edition !== 'steam') throw new Error('Unsupported trace contract');
  if (trace.recordingMode === 'summary-only' || !Array.isArray(trace.actions) || !Array.isArray(trace.randomTape)) throw new Error('Replay requires full recorded actions and random tape; summary-only data cannot be replayed');
  if (!sameEntries(trace.sourceHashes, SOURCE_HASHES)) throw new Error('Trace source hash mismatch');
  if (!sameEntries(trace.adapterSourceHashes, ADAPTER_SOURCE_HASHES)) throw new Error('Trace adapter source hash mismatch or missing pin; older archives are not current-adapter replays');
  if (!sameEntries(trace.executionRuntime, EXECUTION_RUNTIME)) throw new Error('Trace execution runtime mismatch or missing pin (Node, V8, platform, architecture)');
  if (trace.environment?.policyMode !== 'no-retry-no-rng-manipulation') throw new Error('Diagnostic traces do not use the policy action guards');
  if (trace.failure) throw new Error('Trace contains a failed action; it is not a completed-action replay');
  const session = createPolicySession({ sourceDirectory, onTransition, randomTape: [...trace.randomTape], epochMs: trace.environment.epochMs, heralds: trace.environment.heralds,
    maintenanceReload: trace.environment.maintenanceReload });
  for (const action of trace.actions) session.policy.act(action);
  return session;
}

/**
 * Evaluate policy source with JSON observations/actions/memory only. No host callbacks
 * enter this context. This limits capabilities; Node vm is not an OS security boundary.
 */
const compiledPolicies = new Map();
function policyScript(source) {
  if (typeof source !== 'string' || source.length > 1000000) throw new Error('Policy must be bounded JavaScript source');
  if (compiledPolicies.has(source)) return compiledPolicies.get(source);
  const script = new vm.Script(`'use strict';
    globalThis.Date = undefined; globalThis.Intl = undefined; globalThis.Promise = undefined;
    globalThis.WeakRef = undefined; globalThis.FinalizationRegistry = undefined;
    Math.random = () => { throw new Error('Policy RNG access is unavailable'); };
    const input = JSON.parse(__policyInput);
    delete globalThis.__policyInput;
    const freeze = value => { if (value && typeof value === 'object') { Object.values(value).forEach(freeze); Object.freeze(value); } return value; };
    freeze(input);
    const policy = (${source});
    JSON.stringify(policy(input.observation, input.actions, input.memory));`, { filename: 'policy.js' });
  // Reuse parsed code only. Each decision still receives a fresh VM context.
  if (compiledPolicies.size >= 8) compiledPolicies.delete(compiledPolicies.keys().next().value);
  compiledPolicies.set(source, script);
  return script;
}
export function decidePolicy(source, observation, actions, memory = null, { timeoutMs = 1000 } = {}) {
  const script = policyScript(source);
  const input = JSON.stringify({ observation, actions, memory });
  const context = vm.createContext({ __policyInput: input }, { codeGeneration: { strings: false, wasm: false } });
  const result = script.runInContext(context, { timeout: timeoutMs });
  if (typeof result !== 'string') throw new Error('Policy must return a JSON action or {action, memory}');
  return freeze(JSON.parse(result));
}

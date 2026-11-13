import { writeFileSync } from 'node:fs';
import { resolve } from 'node:path';
import { evaluatePolicy, summarizeExperiments } from '../model/evaluate-policy.mjs';
import { baselinePolicySource } from '../model/baseline-policy.mjs';
import { completionPolicySource } from '../model/completion-policy.mjs';

const args = process.argv.slice(2);
const value = (name, fallback) => {
  const index = args.indexOf(name);
  return index < 0 ? fallback : args[index + 1];
};
const horizonMs = Number(value('--seconds', 60)) * 1000;
const summaryOnly = args.includes('--summary-only');
if (summaryOnly && args.includes('--trace')) throw new Error('--summary-only cannot retain a full checkpoint trace; omit --trace');
const seeds = String(value('--seeds', '1')).split(',').map(Number);
const policyName = value('--policy', 'completion-candidate');
if (!['growth', 'completion-candidate'].includes(policyName)) throw new Error('Policy must be growth or completion-candidate');
const source = policyName === 'completion-candidate' ? completionPolicySource({ clickRate: Number(value('--click-rate', 20)) }) : baselinePolicySource({
  clickRate: Number(value('--click-rate', 20)),
  purchaseRule: value('--purchase-rule', 'exchange'),
  upgradeShare: Number(value('--upgrade-share', 0.5)),
});
const results = [];
for (const seed of seeds) {
  if (!Number.isSafeInteger(seed) || seed < 0 || seed > 0xffffffff) throw new Error('Seeds must be uint32 integers');
  const result = evaluatePolicy(source, {
    randomSeed: seed, horizonMs, recordObservations: args.includes('--trace'), recordAudit: !summaryOnly,
    maxDecisions: Number(value('--max-decisions', 100000)),
    maxSameTimeActions: Number(value('--max-same-time-actions', 2000)),
    decisionTimeoutMs: Number(value('--decision-timeout-ms', 1000)),
    progressEveryMs: Number(value('--progress-seconds', 60)) * 1000,
    onProgress: args.includes('--progress') ? progress => console.error(JSON.stringify({seed,...progress,
      rssBytes:process.memoryUsage().rss,heapUsedBytes:process.memoryUsage().heapUsed})) : null,
  });
  results.push(result);
  console.error(JSON.stringify({ seed, status: result.status, elapsedMs: result.observedUntilMs, cookiesEarned: result.observation.cookiesEarned, cookiesPs: result.observation.cookiesPs, missing: result.completion.missing.length, decisions: result.decisions,
    recordingMode:result.audit.recordingMode,actionCount:result.audit.actionCount,randomDrawCount:result.audit.randomDrawCount,error: result.error }));
}
let summary = null;
let summaryError = null;
try { summary = summarizeExperiments(results); }
catch (error) { summaryError = error.message; process.exitCode = 1; }
const output = value('--output', null);
if (output) writeFileSync(resolve(output), `${JSON.stringify({ summary, summaryError, results }, null, 2)}\n`);
console.log(JSON.stringify(summary || { summaryError, scored: false }, null, 2));

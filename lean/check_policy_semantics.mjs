/** Concrete bridge checks for observation memory, binary64 timing, and native clicks. */
import assert from 'node:assert/strict';
import { mkdtempSync, writeFileSync, rmSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { spawnSyncWithFileInput as spawnSync } from './process-input.mjs';
import { fileURLToPath } from 'node:url';
import { decidePolicy } from '../model/policy-runtime.mjs';

const root = fileURLToPath(new URL('./', import.meta.url));
const proofs = [];
const memoryPolicy = '(o, actions, memory) => memory === null ? {action: {type:"wait", milliseconds:20}, memory:{visits:1}} : {type:"click"}';
const frame = { cookies: 17 };
const suggestions = [{ type: 'click' }];
let memory = null;
const expected = [];
for (let i = 0; i < 3; i++) {
  const result = decidePolicy(memoryPolicy, frame, suggestions, memory);
  const repeated = decidePolicy(memoryPolicy, structuredClone(frame), structuredClone(suggestions), structuredClone(memory));
  assert.deepEqual(result, repeated, 'Equal public inputs must give equal decisions');
  if (Object.hasOwn(result, 'action')) { memory = result.memory ?? null; expected.push(result.action); }
  else expected.push(result);
}
assert.deepEqual(memory, { visits: 1 });
assert.deepEqual(expected, [{ type: 'wait', milliseconds: 20 }, { type: 'click' }, { type: 'click' }]);
assert.notDeepEqual(decidePolicy('(o) => Object.keys(o)', { a: 1, b: 2 }, []),
  decidePolicy('(o) => Object.keys(o)', { b: 2, a: 1 }, []),
  'Serialized input order is observable and must not be discarded by the formal interface');
assert.throws(() => decidePolicy('() => Math.random()', frame, suggestions), /RNG access/);
assert.deepEqual(decidePolicy('() => [typeof process, typeof require, typeof Date, typeof Promise, typeof __policyInput, typeof Intl, typeof WeakRef, typeof FinalizationRegistry]', frame, suggestions),
  ['undefined', 'undefined', 'undefined', 'undefined', 'undefined', 'undefined', 'undefined', 'undefined']);
assert.throws(() => decidePolicy('() => new Intl.DateTimeFormat().format()', frame, suggestions), /undefined|DateTimeFormat/);
// Kernel-check the same memory protocol using the JSON values observed above.
const leanJson = value => JSON.stringify(JSON.stringify(value));
proofs.push(`def samplePolicy : Controller := fun _ memory => .ok (if memory == "null" then .remember ${leanJson(expected[0])} ${leanJson(memory)} else .bare ${leanJson(expected[1])})
example : runController samplePolicy "null" (List.replicate 3 { observation := ${leanJson(frame)}, actions := ${leanJson(suggestions)} }) =
    .ok ([${expected.map(leanJson).join(', ')}], ${leanJson(memory)}) := by rfl
`);

let nativeCases = 0;
if (process.argv.includes('--engine')) {
  const { createRuntime } = await import('../model/runtime.mjs');
  const { createPolicySession } = await import('../model/policy-runtime.mjs');
  const { evaluatePolicy, summarizeExperiments } = await import('../model/evaluate-policy.mjs');
  const session = createPolicySession({ randomSeed: 17 });
  assert.deepEqual(Object.keys(session.policy).sort(), ['act', 'actions', 'observe']);
  const observation = session.policy.observe();
  for (const key of ['randomTape', 'randomSeed', 'seed', 'source', 'Game', 'context', 'consumedRandom', 'timers', 'environment']) {
    assert(!Object.hasOwn(observation, key), `Private root channel ${key} must be absent`);
    assert.equal(session.policy[key], undefined);
  }
  assert(Object.isFrozen(observation));
  assert(Object.isFrozen(observation.shop.buildings));

  // Native exact-zero and sub-ULP waits remain possible; the evaluator catches the plateau.
  const stalled = evaluatePolicy('() => ({type:"wait",milliseconds:Number.MIN_VALUE})', {
    horizonMs: 1, maxSameTimeActions: 3,
  });
  assert.equal(stalled.status, 'decision-limit');
  assert.equal(stalled.decisions, 3);
  assert.equal(stalled.observedUntilMs, 0);
  assert.throws(() => summarizeExperiments([stalled]), /cannot be scored/);

  // Nonnegative finite binary64 values are ordered by their normalized raw bit rank.
  const view = new DataView(new ArrayBuffer(8));
  const rank = x => {
    assert(Number.isFinite(x) && x >= 0);
    view.setFloat64(0, x === 0 ? 0 : x, false);
    const value = view.getBigUint64(0, false);
    assert(value < 0x7ff0000000000000n);
    return value;
  };
  const times = [0, Number.MIN_VALUE, 2 ** -20, 2 ** -12, 1, 1000, Number.MAX_SAFE_INTEGER];
  for (let i = 1; i < times.length; i++) assert(rank(times[i - 1]) < rank(times[i]));
  assert.equal(rank(-0), rank(0));
  const clockSession = createPolicySession();
  let prior = { rank: 0n, decisions: 0, sameTime: 0 };
  const reprBudget = s => `{rank := ${s.rank}, decisions := ${s.decisions}, sameTime := ${s.sameTime}}`;
  for (const duration of [0, 2 ** -14, 2 ** -12, 0, 0, 1, 0]) {
    const next = clockSession.policy.act({ type: 'wait', milliseconds: duration });
    const nextRank = rank(next.elapsedMs);
    const after = { rank: nextRank, decisions: prior.decisions + 1,
      sameTime: nextRank === prior.rank ? prior.sameTime + 1 : 0 };
    proofs.push(`example : ClockBudgetStep 3 (${reprBudget(prior)}) (${reprBudget(after)}) := by
  unfold ClockBudgetStep advanceBudget
  decide +kernel
example : BudgetInvariant 3 (${reprBudget(after)}) := by
  unfold BudgetInvariant
  decide +kernel
`);
    assert(prior.sameTime < 3);
    assert(nextRank >= prior.rank);
    prior = after;
    nativeCases++;
  }

  // Track a ghost total of actual accepted native clicks; a raw click can be a no-op.
  const runtime = createRuntime();
  const G = runtime.Game;
  const epoch = Math.floor(runtime.clock.now);
  const reprClick = () => `{clock := ${Math.floor(runtime.clock.now) - epoch}, lastAccepted := ${G.cookieClicks === 0 ? 0 : G.lastClick - epoch}, accepted := ${G.cookieClicks}}`;
  const clickCase = (action, constructor) => {
    const before = reprClick();
    action();
    const after = reprClick();
    proofs.push(`example : ClickStep (${before}) (${after}) := by
  ${constructor}
example : ClickInvariant (${after}) := by
  unfold ClickInvariant
  decide +kernel
`);
    nativeCases++;
  };
  clickCase(() => runtime.advance(100), 'apply ClickStep.wait <;> decide');
  clickCase(() => runtime.act({type:'click'}), 'apply ClickStep.accepted <;> decide');
  assert.equal(G.cookieClicks, 1);
  clickCase(() => runtime.act({type:'click'}), 'exact ClickStep.rejected _');
  const clockBefore = runtime.clock.now;
  for (let i = 0; i < 1000; i++) runtime.act({ type: 'click' });
  assert.equal(runtime.clock.now, clockBefore);
  assert.equal(G.cookieClicks, 1, 'Arbitrarily many same-time calls do not create productive clicks');
  clickCase(() => runtime.advance(19), 'apply ClickStep.wait <;> decide');
  clickCase(() => runtime.act({type:'click'}), 'exact ClickStep.rejected _');
  clickCase(() => runtime.advance(1), 'apply ClickStep.wait <;> decide');
  clickCase(() => runtime.act({type:'click'}), 'apply ClickStep.accepted <;> decide');
  assert.equal(G.cookieClicks, 2);
  assert.match(runtime.source.sources['main.js'], /now-Game\.lastClick<1000\/\(\(e\?e\.detail:1\)===0\?3:50\)/);
}
const directory = mkdtempSync(join(tmpdir(), 'cookie-policy-lean-'));
try {
  const filename = join(directory, 'PolicyBridgeChecks.lean');
  writeFileSync(filename, 'import CookieClicker.PolicySemantics\nopen CookieClicker.FullGame.PolicySemantics\n' + proofs.join('\n'));
  const result = spawnSync('lake', ['env', 'lean', filename], { cwd: root, encoding: 'utf8', maxBuffer: 4 * 1024 * 1024 });
  assert.equal(result.status, 0, result.stdout + result.stderr);
} finally { rmSync(directory, { recursive: true, force: true }); }
console.log(`Policy semantic probes passed: JSON memory protocol and ${nativeCases} kernel-checked native clock/click transitions${nativeCases ? ', including the sub-ULP stall' : ' (--engine enables native probes)'}.`);

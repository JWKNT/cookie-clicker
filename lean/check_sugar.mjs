/** Differential native sugar-clock probes. All fixtures are diagnostic states. */
import assert from 'node:assert/strict';
import { mkdtempSync, writeFileSync, rmSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { spawnSyncWithFileInput as spawnSync } from './process-input.mjs';
import { fileURLToPath } from 'node:url';

if (!process.argv.includes('--engine')) {
  console.log('Native sugar-clock probes require --engine; no source check was claimed.');
  process.exit(0);
}
const { createRuntime } = await import('../model/runtime.mjs');
const root = fileURLToPath(new URL('./', import.meta.url));
const d = 64_436_019;
const kinds = ['normal', 'bifurcated', 'golden', 'meaty', 'caramelized'];
const examples = [];
function fixture({ fast = false, initial = false, random = 0.25 } = {}) {
  const tape = Array(10000).fill(random);
  const runtime = createRuntime({ randomTape: tape });
  const G = runtime.Game;
  const epoch = Math.floor(runtime.clock.now);
  G.lumpsTotal = initial ? -1 : 0; G.lumps = initial ? -1 : 0;
  G.lumpT = epoch; G.lumpCurrentType = 0;
  G.Achievements['Hand-picked'].won = 0;
  if (fast) {
    G.Upgrades['Diabetica Daemonicus'].bought = 1;
    G.Upgrades['Ichor syrup'].bought = 1;
    G.dragonLevel = 27;
    G.dragonAura = G.dragonAurasBN["Dragon's Curve"].id;
    G.dragonAura2 = G.dragonAurasBN['Reality Bending'].id;
  }
  G.computeLumpTimes();
  return { runtime, G, epoch, tape, fast, attempts: 0 };
}
function state(f) {
  const { G, runtime, epoch } = f;
  const clock = Math.floor(runtime.clock.now) - epoch;
  const started = G.lumpT - epoch;
  assert(Number.isSafeInteger(clock) && clock >= 0);
  assert(Number.isSafeInteger(started) && started >= 0, 'These probes use integer timer assignments');
  const initialized = G.lumpsTotal !== -1;
  return `{ clock := ${clock}, started := ${started}, attempts := ${f.attempts}, handPicked := ${!!G.Achievements['Hand-picked'].won}, active := ${!!G.canLumps()}, initialized := ${initialized}, balance := ${initialized ? G.lumps : 0}, total := ${initialized ? G.lumpsTotal : 0}, kind := .${kinds[G.lumpCurrentType]} }`;
}
function record(f, label, action, proof) {
  const before = state(f);
  action();
  const after = state(f);
  examples.push(`-- ${label}\nexample : Step (${before}) (${after}) := by\n  ${proof(f, before, after)}\nexample : Invariant (${after}) := by\n  unfold Invariant\n  decide +kernel\n`);
}
const fastest = '{ diabetica := true, ichor := true, aura := .both : Config }';
const basic = '({} : Config)';
const f = fixture({ fast: true });
f.runtime.clock.now = f.epoch + d - 1;
record(f, 'Immature click does not harvest or reset', () => f.G.clickLump(), () =>
  `apply Step.immatureClick (c := ${fastest})\n  decide +kernel`);
f.runtime.clock.now = f.epoch + d;
record(f, 'Failed first attempt resets the timer', () => { f.G.clickLump(); f.attempts++; }, () =>
  `apply Step.unripeClick (c := ${fastest}) (success := false) (factor := 1) <;> decide +kernel`);
assert.equal(f.G.Achievements['Hand-picked'].won, 0);
f.runtime.clock.now = f.epoch + 2 * d - 1;
record(f, 'Retry one millisecond too early stays immature', () => f.G.clickLump(), () =>
  `apply Step.immatureClick (c := ${fastest})\n  decide +kernel`);
f.tape.fill(0.75);
f.runtime.clock.now = f.epoch + 2 * d;
// The seed-selected second type can change its yield; force normal only in this diagnostic fixture.
f.G.lumpCurrentType = 0;
record(f, 'Successful second attempt observes the same reset rule', () => { f.G.clickLump(); f.attempts++; }, () =>
  `apply Step.unripeClick (c := ${fastest}) (success := true) (factor := 1) <;> decide +kernel`);
assert.equal(f.G.Achievements['Hand-picked'].won, 1);
const gain = fixture({ initial: true });
gain.runtime.clock.now += 100;
record(gain, 'First external ordinary gain initializes counters without moving timer', () => gain.G.gainLumps(3), () =>
  'exact Step.ordinaryGain _ 3');
const activate = fixture({ initial: true });
activate.G.cookiesEarned = 1e9;
activate.runtime.clock.now += 100;
record(activate, 'First native activation starts formation now', () => activate.G.doLumps(), () =>
  'apply Step.activate <;> decide +kernel');
const ripe = fixture();
ripe.runtime.clock.now = ripe.epoch + ripe.G.lumpRipeAge;
record(ripe, 'Ripe click harvests without a Hand-picked attempt', () => ripe.G.clickLump(), () =>
  `apply Step.ripeClick (c := ${basic}) (factor := 1) <;> decide +kernel`);
const exact = fixture();
exact.runtime.clock.now = exact.epoch + exact.G.lumpOverripeAge;
record(exact, 'Exact overripe boundary click is a no-op', () => exact.G.clickLump(), () => 'exact Step.idle _');
const auto = fixture();
auto.runtime.clock.now = auto.epoch + auto.G.lumpOverripeAge + 1;
record(auto, 'Automatic harvest uses the strict overripe guard', () => auto.G.doLumps(), () =>
  `apply Step.automatic (c := ${basic}) (factor := 1) <;> decide +kernel`);
const offline = fixture();
offline.runtime.clock.now = offline.epoch + 3 * offline.G.lumpOverripeAge + 1234;
record(offline, 'Offline catchup advances old start by whole overripe intervals', () => offline.G.loadLumps(), (f, before, after) =>
  `have computed : offline (${before}) ${basic} 3 1 .${kinds[f.G.lumpCurrentType]} = (${after}) := by decide +kernel\n  rw [← computed]\n  apply Step.offlineCatchup (c := ${basic}) (count := 3) (factor := 1) <;> decide +kernel`);
const retype = fixture();
const consumed = retype.runtime.consumedRandom.length;
record(retype, 'Native type selection changes no formation timestamp', () => retype.G.computeLumpType(), () =>
  'exact Step.retype _ _');
assert.equal(retype.runtime.consumedRandom.length, consumed, 'Seeded type draws must not consume the unseeded tape');
const selected = retype.G.lumpCurrentType;
retype.G.computeLumpType();
assert.equal(retype.G.lumpCurrentType, selected, 'Fixed native seed and timestamp determine the type');
retype.runtime.evaluate('Math.random()');
assert.equal(retype.runtime.consumedRandom.length, consumed + 1, 'Native type selection restores unseeded draws');
// Check every assignment to the native formation timer in the pinned main source.
const assignments = [...retype.runtime.source.sources['main.js'].matchAll(/Game\.lumpT\s*=(?!=)([^;]+);/g)].map(m => m[1].trim());
assert.deepEqual(assignments, [
  'Date.now()', "spl[44]?parseInt(spl[44]):Date.now()", 'Date.now()',
  'Math.min(Date.now(),Game.lumpT)', 'Date.now()-(age-amount*Game.lumpOverripeAge)',
  'Date.now()', 'Date.now()',
]);
const directory = mkdtempSync(join(tmpdir(), 'cookie-sugar-lean-'));
try {
  const filename = join(directory, 'NativeSugarChecks.lean');
  writeFileSync(filename, 'import CookieClicker.SugarClock\nopen CookieClicker.FullGame.SugarClock\n' + examples.join('\n'));
  const result = spawnSync('lake', ['env', 'lean', filename], { cwd: root, encoding: 'utf8', maxBuffer: 4 * 1024 * 1024 });
  assert.equal(result.status, 0, result.stdout + result.stderr);
} finally { rmSync(directory, { recursive: true, force: true }); }
console.log(`Native sugar-clock probes passed: ${examples.length} kernel-checked transition projections, all 7 timer assignments, and seeded-type restoration.`);

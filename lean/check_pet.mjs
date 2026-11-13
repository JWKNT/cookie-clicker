/** Native fixed-quarter pet checks. All funded setups are diagnostic fixtures. */
import assert from 'node:assert/strict';
const size = 2 ** 53;
const successes = 450359962737050;
assert.equal(1 / 20, 3602879701896397 / 72057594037927936);
assert((successes - 1) / size < 1 / 20);
assert(!(successes / size < 1 / 20));
assert.equal(successes / size, 225179981368525 / 4503599627370496);

if (!process.argv.includes('--engine')) {
  console.log('Pet finite-kernel boundary checks passed; native probes require --engine.');
  process.exit(0);
}
const { createRuntime } = await import('../model/runtime.mjs');
const tape = Array(100000).fill(0.5);
const runtime = createRuntime({ randomTape: tape });
const G = runtime.Game;
const drops = ['Dragon scale', 'Dragon claw', 'Dragon fang', 'Dragon teddy bear'];
G.Upgrades['Pet the dragon'].bought = 1;
G.dragonLevel = 27; G.specialTab = 'dragon'; G.ToggleSpecialMenu(1);
const now = runtime.clock.now;
const available = () => drops.filter(name => G.Upgrades[name].unlocked || G.Upgrades[name].bought);
assert.deepEqual(available(), []);
for (let n = 0; n < 8; n++) {
  G.ClickSpecialPic();
  assert.equal(runtime.clock.now, now);
  assert.deepEqual(available(), [], 'Failed trigger must not unlock a drop');
}
tape.fill(0.01);
G.ClickSpecialPic();
assert.equal(runtime.clock.now, now);
assert.equal(available().length, 1, 'Success must unlock the fixed missing quarter item');
const selected = available()[0];
for (let n = 0; n < 8; n++) {
  G.ClickSpecialPic();
  assert.equal(runtime.clock.now, now);
  assert.deepEqual(available(), [selected], 'An owned quarter cannot supply another drop');
}
const source = G.ClickSpecialPic.toString();
assert.match(source, /Date\.now\(\)-Game\.lastClickedSpecialPic>2000\) PlaySound\('snd\/growl\.mp3'\)/);
assert.match(source, /Game\.dragonLevel>=8 && Math\.random\(\)<1\/20/);
console.log('Native pet checks passed: repeated same-time failures, one fixed missing-item success, and the already-owned quarter countercase.');

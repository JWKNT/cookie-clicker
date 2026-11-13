/** Pinned RNG call-site audit and native checks. Fixture seeds are not policy inputs. */
import assert from 'node:assert/strict';
import { readFileSync, writeFileSync } from 'node:fs';
import { fileURLToPath } from 'node:url';
import { buildRngPhaseInventory, analyzeFunctionText } from './rng-phase-audit.mjs';

const inventory = buildRngPhaseInventory();
const assumptions = JSON.parse(readFileSync(new URL('../model/mathematical-assumptions.json', import.meta.url), 'utf8'));
assert.equal(assumptions.id, 'iid53-native-seeded-unbounded-clock-strings-fixed-heralds-v3');
assert.equal(assumptions.externalData.heralds.mode, 'fixed');
assert.equal(assumptions.externalData.heralds.value, 100);
assert.equal(assumptions.unseededRandom.bits, 53);
assert.equal(assumptions.timestampStringProcessing.nativePrefixAgreement, true);
assert.match(assumptions.unseededRandom.noArgumentSeedrandom, /Restore the free independent draw law/);
const path = fileURLToPath(new URL('./rng-phase-inventory.json', import.meta.url));
const serialized = `${JSON.stringify(inventory, null, 2)}\n`;
if (process.argv.includes('--write')) writeFileSync(path, serialized);
else assert.equal(readFileSync(path, 'utf8'), serialized, 'RNG inventory is stale; review before --write');

// Mutations must not turn early exits or loop exits into false restoration claims.
assert.deepEqual(analyzeFunctionText('function f() { Math.seedrandom("s"); if (x) return; Math.seedrandom(); }').normalExitPhases, ['free', 'seeded']);
assert.deepEqual(analyzeFunctionText('function f() { while (x) { Math.seedrandom("s"); if (y) return; Math.seedrandom(); } }').normalExitPhases, ['free', 'seeded']);
assert.deepEqual(analyzeFunctionText('function f() { Math.seedrandom("s"); if (x) { Math.seedrandom(); return; } else Math.seedrandom(); }').normalExitPhases, ['free']);
assert.throws(() => analyzeFunctionText('function f() { try { Math.seedrandom("s"); } finally { Math.seedrandom(); } }'), /Unreviewed statement/);

const denominator = 2 ** 53;
for (const index of [0, 1, 2 ** 52 - 1, 2 ** 52, 2 ** 52 + 1, denominator - 1])
  assert.equal(Math.floor((index / denominator) * 2), index >= 2 ** 52 ? 1 : 0);
for (const [lower, upper, letter] of [[32477881928153,313952858638808,0], [4882508249865610,5163983226576265,14]]) {
  assert.equal(BigInt(upper) - BigInt(lower) + 1n, 2n ** 48n);
  for (const index of [lower, lower + 1, Math.floor((lower + upper) / 2), upper - 1, upper]) {
    assert.equal(Math.floor((index / denominator) * 26), letter);
    assert.equal(BigInt(index) * 26n / BigInt(denominator), BigInt(letter));
  }
}

if (process.argv.includes('--engine')) {
  const { createRuntime } = await import('../model/runtime.mjs');
  const runtime = createRuntime({ diagnosticMode: true, randomTape: Array(100000).fill(0.01) });
  const G = runtime.Game;
  const free = runtime.context.Math.random;
  const nativeReseed = runtime.context.Math.seedrandom;
  const reseeds = [];
  runtime.context.Math.seedrandom = function (...args) {
    reseeds.push(args.length ? 'seeded' : 'free');
    return nativeReseed.apply(this, args);
  };
  const check = (name, invoke) => {
    reseeds.length = 0;
    invoke();
    assert.equal(runtime.context.Math.random, free, `${name} leaves a seeded generator`);
    return [...reseeds];
  };
  assert.deepEqual(check('computeLumpType', () => G.computeLumpType()), ['seeded', 'free']);
  for (const name of ['Mice clicking mice', 'Tombola computing'])
    assert.deepEqual(check(name, () => G.Upgrades[name].descFunc()), ['seeded', 'free']);
  G.Upgrades['Fortune cookies'].bought = 1;
  G.fortuneGC = 1; G.fortuneCPS = 0; G.T = G.fps * 10 + 1;
  for (const upgrade of G.Tiers.fortune.upgrades) upgrade.unlocked = 1;
  assert.deepEqual(check('getNewTicker fortuneCPS', () => G.getNewTicker()), ['seeded', 'free']);
  assert.equal(G.TickerEffect.sub, 'fortuneCPS');
  G.Upgrades['Shimmering veil'].bought = 1;
  G.Upgrades['Shimmering veil [off]'].bought = 1;
  G.Upgrades['Reinforced membrane'].bought = 1;
  assert.deepEqual(check('loseShimmeringVeil', () => G.loseShimmeringVeil('click')), ['seeded', 'free']);
  runtime.evaluate(runtime.source.sources['minigameGrimoire.js'], 'minigameGrimoire.js');
  const grimoire = G.Objects['Wizard tower'].minigame;
  grimoire.launch(); grimoire.magic = 1000; grimoire.magicM = 1000;
  assert.deepEqual(check('castSpell', () => grimoire.castSpell(grimoire.spells['conjure baked goods'])), ['seeded', 'free']);
  G.Upgrades['Pet the dragon'].bought = 1;
  G.dragonLevel = 27; G.specialTab = 'dragon'; G.ToggleSpecialMenu(1);
  assert.deepEqual(check('ClickSpecialPic', () => G.ClickSpecialPic()), ['seeded', 'free']);

  const grandma = G.Objects.Grandma;
  grandma.amount = 1; grandma.mouseOn = false;
  assert(check('Grandma.draw', () => grandma.draw()).includes('seeded'));
  const you = G.Objects.You;
  you.amount = 1; you.mouseOn = true; you.mousePos = [32, 32];
  you.draw();
  assert.notEqual(runtime.context.Math.random, free, 'Known You tooltip leak must remain detectable');
  you.mouseOn = false;
  check('You.draw after pointer leave', () => you.draw());

  // Compare the kernel-computed ARC4 witness with actual explicit native seeding.
  runtime.context.Math.seedrandom('aaaao 1 0');
  const actual = Array.from({ length: 3 }, () => runtime.context.Math.random());
  const expected = [7103933198431415 / 18014398509481984, 6524103155113467 / 9007199254740992, 8931643759593147 / 9007199254740992];
  assert.deepEqual(actual, expected);
  for (let count = 2; count <= 20; count++) assert.equal(Math.floor(actual[2] * count), count - 1);
  runtime.context.Math.seedrandom();
  assert.equal(runtime.context.Math.random, free);
  assert(runtime.source.sources['main.js'].includes('function choose(arr) {return arr[Math.floor(Math.random()*arr.length)];}'));
  assert(runtime.source.sources['main.js'].includes('var amount=choose([0,1]);'));
  console.log('RNG audit passed: 23 call sites, 8 callback bodies, early-return mutations, native mode probes, and exact seeded helper witness.');
} else {
  console.log('RNG call-site inventory and finite-kernel boundary checks passed; native probes require --engine.');
}

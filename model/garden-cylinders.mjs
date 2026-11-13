import { createHash } from 'node:crypto';
import { createRuntime } from './runtime.mjs';
import { GARDEN_RECIPES, GARDEN_DROP_CROPS } from './garden-policy.mjs';

const HIGH = 1 - 2 ** -53;
const hash = value => createHash('sha256').update(value).digest('hex');

/** Construct or replay a positive-mass draw cylinder in the unmodified Garden
 * callbacks. This diagnostic advances Garden clock boundaries directly; it is
 * not a full-game wait trace, an executable RNG-selection policy or a proof. */
export function gardenCollectionCylinder({ replayTape = null, secondLog = true } = {}) {
  const runtime = createRuntime({ recordAudit: false }), G = runtime.Game;
  runtime.advance(200);
  const farm = G.Objects.Farm;
  G.cookies = G.cookiesEarned = 2 ** 90;
  farm.amount = farm.highest = farm.bought = 300; farm.level = 10;
  runtime.evaluate(runtime.source.sources['minigameGarden.js'], 'minigameGarden.js');
  const M = farm.minigame; M.launch(); farm.minigameLoaded = true;
  G.CalculateGains();
  const tape = [], rows = [], actions = [];
  let cursor = 0, target = null, mutating = false, spontaneous = false, uproot = false;
  let candidates = [], candidateIndex = 0, gardenTicks = 0, plantingCount = 0, quotedPlantCost = 0;
  const originalMuts = M.getMuts;
  if (!replayTape) M.getMuts = function (...args) {
    const result = originalMuts.apply(this, args);
    candidates = result; candidateIndex = 0;
    return result;
  };
  const lines = runtime.source.sources['minigameGarden.js'].split('\n');
  const callSites = {};
  for (const [key, needle] of Object.entries({ growth: 'tile[1]+=randomFloor(', mutation: 'Math.random()<muts[ii][1]',
    weed: 'Math.random()<chance', kill: 'Math.random()<0.2*(age/100)', drop: 'Math.random()<=rate*Game.dropRateMult()' })) {
    const index = lines.findIndex(line => line.includes(needle));
    if (index < 0) throw new Error(`Pinned Garden call site missing: ${key}`);
    callSites[key] = { line: index + 1, column: lines[index].indexOf('Math.random') + 6 };
  }
  runtime.context.Math.random = () => {
    let bit;
    if (replayTape) {
      if (cursor >= replayTape.length) throw new Error('Garden cylinder replay exhausted');
      bit = replayTape[cursor];
    } else {
      const stack = new Error().stack;
      const match = stack.match(/minigameGarden\.js:(\d+):(\d+)/);
      const line = +match?.[1], column = +match?.[2];
      bit = 1;
      if (line === callSites.growth.line) bit = 0;
      else if (line === callSites.mutation.line) {
        if (column === callSites.mutation.column) {
          const candidate = candidates[candidateIndex++];
          if (!candidate) throw new Error('Mutation draw did not match its native candidate');
          bit = mutating && candidate[0] === target ? 0 : 1;
        } else bit = 0; // Chosen weed/fungus candidate's positive eligibility guard.
      } else if (line === callSites.weed.line) bit = spontaneous ? 0 : 1;
      else if (line === callSites.kill.line) {
        if (stack.includes('at choose ')) bit = uproot && target === 'crumbspore' ? 1 : 0;
        else bit = uproot ? 0 : 1;
      } else if (line === callSites.drop.line) bit = 0;
    }
    if (bit !== 0 && bit !== 1) throw new Error('Invalid Garden cylinder bit');
    cursor++; tape.push(bit);
    return bit ? HIGH : 0;
  };
  const cells = () => M.plot.flatMap((row, y) => row.map((tile, x) => ({ x, y, tile,
    plant: tile[0] ? M.plantsById[tile[0] - 1] : null }))).filter(cell => cell.plant);
  const tick = () => {
    const before = M.nextStep;
    runtime.clock.now = Math.max(runtime.clock.now + 1, M.nextStep);
    M.logic(); G.CalculateGains(); gardenTicks++;
    if (!(M.nextStep > before)) throw new Error('Garden tick failed to advance');
    actions.push({ type: 'garden-tick', milliseconds: M.stepT * 1000 });
  };
  const harvest = cell => { M.harvest(cell.x, cell.y, 1); actions.push({ type: 'garden-harvest', x: cell.x, y: cell.y }); };
  const clear = keep => {
    const wasUproot = uproot; uproot = false;
    for (let pass = 0; pass < 2; pass++) for (const cell of cells())
      if (!keep || cell.x !== keep.x || cell.y !== keep.y) harvest(cell);
    uproot = wasUproot;
    if (cells().some(cell => !keep || cell.x !== keep.x || cell.y !== keep.y)) throw new Error('Bounded two-pass cleanup failed');
  };
  const plant = (key, x, y) => {
    const p = M.plants[key], price = M.getCost(p);
    if (!p.unlocked || p.plantable === false || !M.canPlant(p)) throw new Error(`Unavailable plant ${key}`);
    const before = G.cookies; M.useTool(p.id, x, y);
    if (M.plot[y][x][0] !== p.id + 1) throw new Error(`Planting failed: ${key}`);
    plantingCount++; quotedPlantCost += price;
    actions.push({ type: 'garden-plant', seed: key, x, y, price, nativeDebit: before - G.cookies });
  };
  const mature = cell => {
    for (let i = 0; i < 100 && M.plot[cell.y][cell.x][1] < M.plantsById[M.plot[cell.y][cell.x][0] - 1]?.mature; i++) tick();
    const tile = M.plot[cell.y][cell.x], p = M.plantsById[tile[0] - 1];
    if (!p || tile[1] < p.mature) throw new Error('Isolated maturation failed');
    return { ...cell, tile, plant: p };
  };
  const collectLog = log => {
    for (const recipe of GARDEN_RECIPES) {
      clear(); target = recipe.target; mutating = spontaneous = uproot = false;
      const startTicks = gardenTicks, startDraw = cursor, startActions = actions.length;
      if (recipe.kind === 'spontaneous') { spontaneous = true; tick(); spontaneous = false; }
      else if (recipe.kind === 'uproot') {
        plant('meddleweed', 2, 2); mature({ x: 2, y: 2 });
        uproot = true; harvest({ x: 2, y: 2 }); uproot = false;
      } else if (target === 'everdaisy') {
        for (const x of [1, 2, 3]) plant('elderwort', x, 1);
        for (let i = 0; i < 90; i++) tick();
        for (const x of [1, 2, 3]) plant('tidygrass', x, 3);
        for (let i = 0; i < 40; i++) tick();
        mutating = true; tick(); mutating = false;
      } else {
        const parents = Object.entries(recipe.parents).flatMap(([key, count]) => Array.from({ length: count }, () => key));
        const positions = parents.length === 8
          ? [[1,1],[2,1],[3,1],[1,2],[3,2],[1,3],[2,3],[3,3]]
          : [[1,1],[3,3],[3,1]];
        const durations = parents.map(key => Math.ceil(M.plants[key].mature / Math.ceil(M.plants[key].ageTick)));
        const finish = Math.max(...durations);
        for (let time = 0; time < finish; time++) {
          parents.forEach((key, i) => { if (time === finish - durations[i]) plant(key, ...positions[i]); });
          tick();
        }
        mutating = true; tick(); mutating = false;
      }
      const selected = cells().find(cell => cell.plant.key === target);
      if (!selected) throw new Error(`No target mutation: ${target}`);
      clear(selected); const ripe = mature(selected); harvest(ripe); clear();
      if (!M.plants[target].unlocked) throw new Error(`Seed not unlocked: ${target}`);
      rows.push({ log, target, ticks: gardenTicks - startTicks, draws: cursor - startDraw,
        actions: actions.length - startActions, unlocked: true });
    }
    if (M.plantsUnlockedN !== M.plantsN) throw new Error('Garden log incomplete');
  };
  collectLog(1);
  if (secondLog) {
    M.askConvert(); runtime.act({ type: 'prompt', option: 0 }, { observe: false });
    if (!G.HasAchiev('Seedless to nay')) throw new Error('Native Garden sacrifice failed');
    collectLog(2);
  }
  target = null;
  for (const crop of GARDEN_DROP_CROPS) {
    clear(); plant(crop.crop, 2, 2); harvest(mature({ x: 2, y: 2 })); clear();
    if (!G.Upgrades[crop.upgrade].unlocked) throw new Error(`Garden upgrade did not drop: ${crop.upgrade}`);
    G.Upgrades[crop.upgrade].buy();
  }
  while (M.harvestsTotal < 1000) {
    for (let y = 0; y < 6; y++) for (let x = 0; x < 6; x++) plant('thumbcorn', x, y);
    for (let tickNo = 0; tickNo < 4; tickNo++) tick();
    clear();
  }
  if (replayTape && cursor !== replayTape.length) throw new Error('Garden cylinder replay left unused draws');
  return { schemaVersion: 1, scope: 'Garden-callback-cylinder-with-funded-entry-and-clock-jump-premises',
    sourceHashes: runtime.source.hashes,
    premises: ['Bank/earned=2^90, Farm amount300 and level10 are assigned',
      'Only Garden logic and gain recomputation run at exact nextStep boundaries; intervening full-game timers are not executed',
      'The diagnostic draw selector constructs an event; a legal strategy cannot select its random outcomes'],
    open: ['Refine Garden deadline jumps to full-game native waits and bound all intervening draw counts',
      'Prove uniform resource and maturity/growth invariants at every retry entry',
      'Kernel-check callback execution and compose the resulting success bound with the full completion route'],
    recovery: 'Two native harvest passes clear any6x6 plot; meddleweed can spawn only a child with no onKill replacement',
    iidEvent: { drawCount: cursor, probability: `2^(-${53 * cursor})`, outcomes: ['0', '1-2^-53'] },
    rows, gardenTicks, plantingCount, quotedPlantCost, bankAfter: G.cookies,
    harvestsTotal: M.harvestsTotal, seedCount: M.plantsUnlockedN,
    seedless: !!G.HasAchiev('Seedless to nay'), fullPlot: !!G.HasAchiev('In the garden of Eden (baby)'),
    gardenDrops: GARDEN_DROP_CROPS.map(crop => ({ ...crop, bought: !!G.Has(crop.upgrade) })),
    tapeSha256: hash(Buffer.from(tape)), actionsSha256: hash(JSON.stringify(actions)), tape,
  };
}

export function probeGardenRecovery() {
  const runtime = createRuntime({ recordAudit: false }); runtime.advance(200);
  const G = runtime.Game, farm = G.Objects.Farm;
  farm.amount = 300; farm.level = 10; G.cookies = G.cookiesEarned = 2 ** 90;
  runtime.evaluate(runtime.source.sources['minigameGarden.js'], 'minigameGarden.js');
  const M = farm.minigame; M.launch(); farm.minigameLoaded = true;
  const replacingPlants = Object.values(M.plants).filter(plant => plant.onKill).map(plant => plant.key);
  const childCallbacksAbsent = ['brownMold', 'crumbspore'].every(key => !M.plants[key].onKill);
  const result = [];
  for (const chooseHigh of [false, true]) {
    for (let y = 0; y < 6; y++) for (let x = 0; x < 6; x++) M.plot[y][x] = [M.plants.meddleweed.id + 1, 99];
    let draws = 0, harvestCalls = 0;
    runtime.context.Math.random = () => { draws++; return chooseHigh && new Error().stack.includes('at choose ') ? HIGH : 0; };
    const original = M.harvest;
    M.harvest = function (...args) { harvestCalls++; return original.apply(this, args); };
    M.harvestAll(); M.harvest = original;
    result.push({ replacement: chooseHigh ? 'crumbspore' : 'brownMold', draws, harvestCalls,
      remainingPlants: M.plot.flat().filter(tile => tile[0] > 0).length });
  }
  return { scope: 'native-two-pass-recovery-fixtures', premises: ['Assign36 age99 meddleweeds; force every possible onKill replacement branch'],
    sourceHashes: runtime.source.hashes, replacingPlants, childCallbacksAbsent, result };
}

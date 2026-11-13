import { planGoldenGarden } from './golden-garden.mjs';

const naturalCookiePlot = planGoldenGarden().plot;

/** A constructive Garden controller. It is a baseline policy, not an optimum. */
export const GARDEN_RECIPES = Object.freeze([
  { target: 'meddleweed', kind: 'spontaneous', parents: {} },
  { target: 'brownMold', kind: 'uproot', parents: { meddleweed: 1 } },
  { target: 'crumbspore', kind: 'uproot', parents: { meddleweed: 1 } },
  { target: 'thumbcorn', parents: { bakerWheat: 2 }, candidateProbability: 0.05 },
  { target: 'cronerice', parents: { bakerWheat: 1, thumbcorn: 1 }, candidateProbability: 0.01 },
  { target: 'gildmillet', parents: { cronerice: 1, thumbcorn: 1 }, candidateProbability: 0.03 },
  { target: 'clover', parents: { bakerWheat: 1, gildmillet: 1 }, candidateProbability: 0.03 },
  { target: 'shimmerlily', parents: { clover: 1, gildmillet: 1 }, candidateProbability: 0.02 },
  { target: 'elderwort', parents: { shimmerlily: 1, cronerice: 1 }, candidateProbability: 0.01 },
  { target: 'ichorpuff', parents: { elderwort: 1, crumbspore: 1 }, candidateProbability: 0.002 },
  { target: 'bakeberry', parents: { bakerWheat: 2 }, candidateProbability: 0.001 },
  { target: 'chocoroot', parents: { bakerWheat: 1, brownMold: 1 }, candidateProbability: 0.1, immatureParents: ['brownMold'] },
  { target: 'whiteMildew', parents: { brownMold: 1 }, candidateProbability: 0.5 },
  { target: 'whiteChocoroot', parents: { chocoroot: 1, whiteMildew: 1 }, candidateProbability: 0.1, immatureParents: ['whiteMildew'] },
  { target: 'whiskerbloom', parents: { shimmerlily: 1, whiteChocoroot: 1 }, candidateProbability: 0.01 },
  { target: 'chimerose', parents: { shimmerlily: 1, whiskerbloom: 1 }, candidateProbability: 0.05 },
  { target: 'nursetulip', parents: { whiskerbloom: 2 }, candidateProbability: 0.05 },
  { target: 'greenRot', parents: { whiteMildew: 1, clover: 1 }, candidateProbability: 0.05 },
  { target: 'keenmoss', parents: { greenRot: 1, brownMold: 1 }, candidateProbability: 0.1 },
  { target: 'drowsyfern', parents: { chocoroot: 1, keenmoss: 1 }, candidateProbability: 0.005 },
  { target: 'wardlichen', parents: { cronerice: 1, whiteMildew: 1 }, candidateProbability: 0.005 },
  { target: 'queenbeet', parents: { chocoroot: 1, bakeberry: 1 }, candidateProbability: 0.01 },
  { target: 'queenbeetLump', parents: { queenbeet: 8 }, candidateProbability: 0.001 },
  { target: 'duketater', parents: { queenbeet: 2 }, candidateProbability: 0.001 },
  { target: 'doughshroom', parents: { crumbspore: 2 }, candidateProbability: 0.005 },
  { target: 'glovemorel', parents: { crumbspore: 1, thumbcorn: 1 }, candidateProbability: 0.02 },
  { target: 'cheapcap', parents: { crumbspore: 1, shimmerlily: 1 }, candidateProbability: 0.04 },
  { target: 'foolBolete', parents: { doughshroom: 1, greenRot: 1 }, candidateProbability: 0.04 },
  { target: 'wrinklegill', parents: { crumbspore: 1, brownMold: 1 }, candidateProbability: 0.06 },
  { target: 'shriekbulb', parents: { duketater: 3 }, candidateProbability: 0.005, immatureParents: ['duketater'] },
  { target: 'tidygrass', parents: { bakerWheat: 1, whiteChocoroot: 1 }, candidateProbability: 0.002 },
  { target: 'everdaisy', parents: { tidygrass: 3, elderwort: 3 }, candidateProbability: 0.002 },
  { target: 'goldenClover', parents: { bakerWheat: 1, gildmillet: 1 }, candidateProbability: 0.0007 },
]);

export const GARDEN_DROP_CROPS = Object.freeze([
  { upgrade: 'Ichor syrup', crop: 'ichorpuff', rate: 0.005 },
  { upgrade: 'Wheat slims', crop: 'bakerWheat', rate: 0.001 },
  { upgrade: 'Elderwort biscuits', crop: 'elderwort', rate: 0.01 },
  { upgrade: 'Bakeberry cookies', crop: 'bakeberry', rate: 0.015 },
  { upgrade: 'Fern tea', crop: 'drowsyfern', rate: 0.01 },
  { upgrade: 'Duketater cookies', crop: 'duketater', rate: 0.005 },
  { upgrade: 'Green yeast digestives', crop: 'greenRot', rate: 0.005 },
]);

function gardenDecision(observation, availableActions, memory, recipes, dropCrops, cookiePlot) {
  memory ||= {};
  const config = { farmDrops: true, harvestTarget: 1000, requireFullPlot: true,
    boostNovelGrowth: true, novelGrowthMaxCostFraction: 0.01, naturalCookieFarm: false,
    sacrificesRequired: 1, maxWaitMs: 1000, fixedSoil: null, ...(memory.config || {}) };
  const nextMemory = { ...memory, config };
  const G = observation.garden;
  const result = (status, goal, reason, action = null, extra = {}) =>
    ({ status, goal, reason, action, memory: nextMemory, ...extra });
  if (config.fixedSoil !== null && !['dirt', 'fertilizer', 'clay', 'woodchips'].includes(config.fixedSoil))
    return result('blocked', 'Garden configuration', 'Use a supported fixed soil or null.');
  if (!G?.ready) return result('needs-resources', 'Garden access', 'Farm level 1 and the loaded Garden are required.');
  if (observation.progression?.onAscend || observation.progression?.ascensionMode !== 0) {
    return result('blocked', 'Active Garden', 'The controller requires an active normal run.');
  }
  const seedKeys = ['bakerWheat', ...recipes.map(x => x.target)];
  if (seedKeys.some(key => !G.plants[key]) || Object.keys(G.plants).length !== 34) {
    return result('blocked', 'Pinned seed catalogue', 'The observed Garden does not match all 34 supported seeds.');
  }
  const limits = [[2,2,4,4], [2,2,5,4], [2,2,5,5], [1,2,5,5], [1,1,5,5],
    [1,1,6,5], [1,1,6,6], [0,1,6,6], [0,0,6,6]][Math.max(0, Math.min(8, G.level - 1))];
  const cells = [];
  for (let y = limits[1]; y < limits[3]; y++) for (let x = limits[0]; x < limits[2]; x++) {
    const [key, age] = G.plot[y][x];
    cells.push({ x, y, key, age, plant: key ? G.plants[key] : null });
  }
  const known = key => G.plants[key].unlocked;
  const isMature = cell => !!cell.key && cell.age >= cell.plant.mature;
  const harvest = (cell, goal, reason) => result('acting', goal, reason, { type: 'garden-harvest', x: cell.x, y: cell.y });
  const wait = (goal, reason) => result('waiting', goal, reason, {
    type: 'wait', milliseconds: Math.max(1, Math.min(config.maxWaitMs, G.nextStepMs > 0 ? G.nextStepMs : 1000 / 30)),
  }, { wakeAfterMs: G.nextStepMs });
  const soil = (preferred, goal) => {
    preferred = config.fixedSoil ?? preferred;
    const required = { dirt: 0, fertilizer: 50, clay: 100, woodchips: 300 }[preferred];
    if (G.soil !== preferred && G.farmAmount >= required && G.nextSoilMs <= 0) {
      return result('acting', goal, `Use ${preferred} for this stage.`, { type: 'garden-soil', soil: preferred });
    }
    return null;
  };
  const plant = (cell, key, goal) => {
    const p = G.plants[key];
    if (!p.unlocked || !p.plantable) return result('blocked', goal, `Seed ${key} cannot be planted.`);
    if (observation.cookies < p.cost) return result('needs-resources', goal, `Planting ${key} requires more cookies.`, null, { requiredCookies: p.cost, seed: key });
    return result('acting', goal, `Plant ${key}.`, { type: 'garden-plant', seed: key, x: cell.x, y: cell.y });
  };

  const allKnown = seedKeys.every(known);
  if (memory.confirmSacrifice) {
    if (G.seedless && G.convertTimes >= config.sacrificesRequired) delete nextMemory.confirmSacrifice;
    else if (allKnown && observation.controls?.promptOn) {
      delete nextMemory.confirmSacrifice;
      delete nextMemory.target;
      return result('acting', 'Garden sacrifice', 'Confirm the sacrifice requested by this controller.', { type: 'prompt', option: 0 });
    } else {
      delete nextMemory.confirmSacrifice;
      return result('blocked', 'Garden sacrifice', 'The expected sacrifice prompt is absent or the seed log changed.');
    }
  }
  if (observation.controls?.promptOn) return result('blocked', 'Garden control', 'Resolve the current unrelated prompt first.');
  if (G.freeze) return result('acting', 'Garden growth', 'Unfreeze the Garden before the next growth step.', { type: 'garden-freeze' });

  if (config.fixedSoil !== null && G.soil !== config.fixedSoil) {
    return soil(config.fixedSoil, 'Fixed collection soil') || wait('Fixed collection soil', 'Wait for the native soil cooldown before collection.');
  }

  // New seeds take priority over parent replacement and the next recipe.
  const novel = cells.filter(cell => cell.key && !known(cell.key));
  const matureNovel = novel.find(isMature);
  if (matureNovel) return harvest(matureNovel, matureNovel.key, 'Harvest the mature plant to add its seed to the log.');
  if (novel.length) {
    const adjacent = (a, b) => (a.x !== b.x || a.y !== b.y)
      && Math.abs(a.x - b.x) <= 1 && Math.abs(a.y - b.y) <= 1;
    const slowKeys = ['queenbeetLump', 'drowsyfern', 'everdaisy', 'duketater'];
    // Native computeBoostPlot applies elderwort's age effect directly. Its
    // strength depends on soil and elderwort age, not surrounding power boosts.
    // In particular, juicy queenbeet attenuation does not weaken this effect.
    const helpful = cell => config.boostNovelGrowth && cell.key === 'elderwort'
      && novel.some(target => slowKeys.includes(target.key) && adjacent(cell, target))
      && !novel.some(target => !slowKeys.includes(target.key) && adjacent(cell, target));
    const unwanted = cells.find(cell => cell.key && known(cell.key) && !helpful(cell));
    if (unwanted) return harvest(unwanted, novel[0].key, 'Remove known plants while the new seed grows.');
    const betterSoil = soil('fertilizer', novel[0].key);
    if (betterSoil) return betterSoil;
    // Buying support plants trades cookies for growth. Keep this optional and
    // cheap relative to the current bank; never block maturation for its cost.
    // These slow crops cannot jump from immature to dead in one boosted step.
    const slow = novel.filter(cell => slowKeys.includes(cell.key)
      && (cell.plant.mature - cell.age) / (cell.plant.ageTick + cell.plant.ageTickR / 2) >= 100);
    const elderwort = G.plants.elderwort;
    if (config.boostNovelGrowth && elderwort.unlocked && elderwort.plantable
      && elderwort.cost <= observation.cookies * Math.max(0, Math.min(1, config.novelGrowthMaxCostFraction))) {
      const support = cells.filter(cell => !cell.key)
        .filter(cell => !novel.some(target => !slowKeys.includes(target.key) && adjacent(cell, target)))
        .map(cell => ({ ...cell, targets: slow.filter(target => adjacent(cell, target)).length }))
        .filter(cell => cell.targets > 0).sort((a, b) => b.targets - a.targets)[0];
      if (support) return plant(support, 'elderwort', slow[0].key);
    }
    return wait(novel[0].key, 'Wait for the new plant to mature.');
  }

  if (allKnown && (!G.seedless || G.convertTimes < config.sacrificesRequired)) {
    nextMemory.confirmSacrifice = true;
    return result('acting', 'Garden sacrifice', 'The full seed log is ready for the required sacrifice.', { type: 'garden-sacrifice' });
  }

  // After the final rebuild, grow the seven upgrade drops and other Garden goals.
  if (allKnown) {
    delete nextMemory.target;
    const missingDrop = config.farmDrops ? dropCrops.find(x => !observation.upgrades?.[x.upgrade]?.unlocked
      && !observation.upgrades?.[x.upgrade]?.bought) : null;
    const needsFullPlot = config.requireFullPlot && !observation.achievements?.['In the garden of Eden (baby)'];
    if (needsFullPlot && G.level < 9) return result('needs-level', 'Full Garden plot', 'Farm level 9 is required for all 36 plots.', null, { building: 'Farm', level: 9 });
    const needsHarvests = G.harvestsTotal < config.harvestTarget;
    if (!missingDrop && !needsHarvests && !needsFullPlot) {
      if (config.naturalCookieFarm && !observation.achievements?.["Black cat's paw"]) {
        const goal = "Black cat's paw";
        if (G.level < 9) return result('needs-level', goal, 'The cookie-count layout requires the full plot.', null, { building: 'Farm', level: 9 });
        if (G.farmAmount < 100) return result('needs-resources', goal, 'Clay requires 100 Farms.', null, { building: 'Farm', amount: 100 });
        // This maximizes only the mature two-crop clay frequency. Plant costs,
        // growth, death, CpS loss, and the other goals remain scheduling costs.
        // Never harvest a mature crop merely because it is mature in this phase.
        const wrong = cells.find(cell => cell.key && cell.key !== cookiePlot[cell.y][cell.x]);
        if (wrong) return harvest(wrong, goal, 'Clear a plant outside the cookie-count layout.');
        const betterSoil = soil('clay', goal);
        if (betterSoil) return betterSoil;
        const empty = cells.filter(cell => !cell.key).sort((a, b) =>
          Number(cookiePlot[b.y][b.x] === 'nursetulip') - Number(cookiePlot[a.y][a.x] === 'nursetulip'))[0];
        if (empty) return plant(empty, cookiePlot[empty.y][empty.x], goal);
        return wait(goal, 'Keep the frequency crops and replace plants after they die.');
      }
      return result('complete', 'Garden goals', 'All seeds are rebuilt and the configured Garden goals are satisfied.');
    }
    const crop = needsFullPlot ? 'thumbcorn' : missingDrop?.crop || 'thumbcorn';
    const goal = needsFullPlot ? 'In the garden of Eden (baby)' : missingDrop?.upgrade || 'Green, aching thumb';
    // Adjacent ichorpuffs multiply growth penalties. Grow isolated plants.
    const cropCells = crop === 'ichorpuff'
      ? cells.filter(cell => (cell.x - limits[0]) % 2 === 0 && (cell.y - limits[1]) % 2 === 0) : cells;
    const cropCoordinates = new Set(cropCells.map(cell => `${cell.x},${cell.y}`));
    const wrong = cells.find(cell => cell.key && (cell.key !== crop || !cropCoordinates.has(`${cell.x},${cell.y}`)));
    if (wrong) return harvest(wrong, goal, 'Clear the previous crop.');
    const mature = cropCells.find(isMature);
    if (mature && !needsFullPlot) return harvest(mature, goal, 'Harvest the mature crop for its upgrade drop or harvest count.');
    const empty = cropCells.find(cell => !cell.key);
    if (empty) return plant(empty, crop, goal);
    if (mature) return wait(goal, 'Allow native Garden updates to register the full plot before harvesting.');
    return soil('fertilizer', goal) || wait(goal, 'Grow the crop to maturity.');
  }

  let recipe = recipes.find(x => x.target === memory.target && !known(x.target)
    && Object.keys(x.parents).every(known));
  recipe ||= recipes.find(x => !known(x.target) && Object.keys(x.parents).every(known));
  if (!recipe) return result('blocked', 'Seed collection', 'No supported recipe has its prerequisite seeds.');
  nextMemory.target = recipe.target;
  const goal = recipe.target;

  if (recipe.kind === 'spontaneous') {
    const occupied = cells.find(cell => cell.key);
    if (occupied) return harvest(occupied, goal, 'Empty the plot so meddleweed can appear without neighbors.');
    return soil(G.farmAmount >= 50 ? 'fertilizer' : 'dirt', goal) || wait(goal, 'Wait for spontaneous meddleweed.');
  }
  if (recipe.kind === 'uproot') {
    const wrong = cells.find(cell => cell.key && cell.key !== 'meddleweed');
    if (wrong) return harvest(wrong, goal, 'Clear the previous crop.');
    const oldWeed = cells.find(cell => cell.key === 'meddleweed' && cell.age >= 80);
    if (oldWeed) return harvest(oldWeed, goal, 'Uproot old meddleweed for a chance to release brown mold or crumbspore.');
    const empty = cells.find(cell => !cell.key);
    if (empty) return plant(empty, 'meddleweed', goal);
    return soil('fertilizer', goal) || wait(goal, 'Let meddleweed age before uprooting it.');
  }

  const parentKeys = Object.entries(recipe.parents).flatMap(([key, n]) => Array(n).fill(key));
  const neighborhoods = cells.map(center => ({ center, neighbors: cells.filter(cell =>
    (cell.x !== center.x || cell.y !== center.y) && Math.abs(cell.x - center.x) <= 1 && Math.abs(cell.y - center.y) <= 1) }));
  const singleLayout = neighborhoods.find(x => x.neighbors.length >= parentKeys.length);
  if (!singleLayout) return result('needs-level', goal, 'This recipe requires a larger adjacent planting area.', null, { building: 'Farm', level: 3 });
  // Four disjoint 3x3 blocks fit in the full plot. In particular this provides
  // four valid eight-queenbeet rings instead of only one mutation opportunity.
  const parallelLayouts = [];
  for (let y = limits[1] + 1; y + 1 < limits[3]; y += 3) {
    for (let x = limits[0] + 1; x + 1 < limits[2]; x += 3) {
      parallelLayouts.push(neighborhoods.find(layout => layout.center.x === x && layout.center.y === y));
    }
  }
  const layouts = parallelLayouts.length ? parallelLayouts : [singleLayout];
  const beds = layouts.map(layout => ({ id: `${layout.center.x},${layout.center.y}`,
    parents: layout.neighbors.slice(0, parentKeys.length).map((cell, i) => ({ ...cell, wanted: parentKeys[i] })) }));
  const assigned = beds.flatMap(bed => bed.parents);
  const assignments = new Map(assigned.map(cell => [`${cell.x},${cell.y}`, cell.wanted]));
  const wrong = cells.find(cell => cell.key && assignments.get(`${cell.x},${cell.y}`) !== cell.key);
  if (wrong) return harvest(wrong, goal, 'Clear a competing plant from the mutation layout.');
  nextMemory.beds = memory.target === goal ? { ...(memory.beds || {}) } : {};
  for (const bed of beds) {
    let stage = nextMemory.beds[bed.id] || 'starting';
    // A missing parent after establishment means a death or contamination.
    // Restart the whole bed so the eight queenbeets can mature together again.
    if (stage === 'established' && bed.parents.some(cell => !cell.key)) stage = 'clearing';
    if (stage === 'clearing') {
      const remainingParent = bed.parents.find(cell => cell.key);
      if (remainingParent) {
        nextMemory.beds[bed.id] = stage;
        return harvest(remainingParent, goal, 'Restart this mutation bed after a parent was lost.');
      }
      stage = 'starting';
    }
    if (bed.parents.every(cell => cell.key)) stage = 'established';
    nextMemory.beds[bed.id] = stage;
  }
  const duration = (key, age = 0) => Math.max(0, G.plants[key].mature - age)
    / (G.plants[key].ageTick + G.plants[key].ageTickR / 2);
  const immatureAllowed = key => (recipe.immatureParents || []).includes(key);
  const remaining = cell => immatureAllowed(cell.wanted) ? 0 : duration(cell.wanted, cell.key ? cell.age : 0);
  const toPlant = beds.flatMap(bed => {
    const longest = Math.max(...bed.parents.map(remaining));
    return bed.parents.filter(cell => !cell.key && remaining(cell) + 1 >= longest);
  })[0];
  if (toPlant) return plant(toPlant, toPlant.wanted, goal);
  const ready = beds.some(bed => bed.parents.every(cell => cell.key === cell.wanted && (immatureAllowed(cell.wanted) || isMature(cell))));
  if (ready) return soil('woodchips', goal) || wait(goal, 'Keep mature parents around the empty mutation tile.');
  return soil('fertilizer', goal) || wait(goal, 'Grow slower parents first, then plant the faster parents.');
}

export function decideGardenAction(observation, memory = {}, options = {}) {
  return gardenDecision(observation, [], { ...memory, config: { ...(memory.config || {}), ...options } }, GARDEN_RECIPES, GARDEN_DROP_CROPS, naturalCookiePlot);
}

/** Self-contained source for the capability-limited policy evaluator. */
export function gardenPolicySource(options = {}) {
  return `(function(observation, availableActions, memory) {
    const decision = ${gardenDecision.toString()};
    return decision(observation, availableActions, {...(memory || {}), config: {...${JSON.stringify(options)}, ...((memory || {}).config || {})}},
      ${JSON.stringify(GARDEN_RECIPES)}, ${JSON.stringify(GARDEN_DROP_CROPS)}, ${JSON.stringify(naturalCookiePlot)});
  })`;
}

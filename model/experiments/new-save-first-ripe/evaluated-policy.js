(function () {
    const grow = ((function () {
    const config = {"clickRate":50,"purchaseRule":"exchange","upgradeShare":0.5,"inputBatchMilliseconds":1000,"purchaseIntervalMilliseconds":300};
    return function (observation, actions, memory) {
      const m = memory ? { ...memory } : { nextClick: 100, nextPurchase: 0 };
      const t = observation.elapsedMs;
      const answer = action => ({ action, memory: m });
      if (observation.progression.onAscend || observation.progression.ascendTimer || observation.progression.reincarnateTimer) return answer({type:'wait',milliseconds:100});
      const shimmer = observation.shimmers[0];
      if (shimmer) return answer({type:'click-shimmer',id:shimmer.id});
      if (config.clickRate > 0 && t >= m.nextClick) {
        m.nextClick = t + 1000 / config.clickRate;
        return answer({type:'click'});
      }
      if (t >= m.nextPurchase) {
        m.nextPurchase = t + config.purchaseIntervalMilliseconds;
        const upgrade = observation.shop.upgrades
          .filter(u => u.pool !== 'toggle' && u.pool !== 'prestige' && u.canBuy && u.price <= observation.cookies * config.upgradeShare)
          .sort((a,b) => a.price-b.price || a.id-b.id)[0];
        if (upgrade) return answer({type:'buy-upgrade',id:upgrade.id});
        const buildings = observation.shop.buildings.filter(b => !b.locked && b.storedCps > 0);
        const totalBase = observation.shop.buildings.reduce((sum,b) => sum+b.storedTotalCps,0);
        const multiplier = totalBase > 0 ? observation.cookiesPs / totalBase : 1;
        const income = Math.max(observation.cookiesPs,0.1);
        const score = b => config.purchaseRule === 'cheapest' ? b.buy1price
          : config.purchaseRule === 'roi' ? b.buy1price / Math.max(b.storedCps*multiplier,0.000001)
          : Math.max(b.buy1price-observation.cookies,0)/income + b.buy1price/Math.max(b.storedCps*multiplier,0.000001);
        buildings.sort((a,b) => score(a)-score(b) || a.id-b.id);
        const best = buildings[0];
        if (best && best.buy1price <= observation.cookies) return answer({type:'buy-building',id:best.id,amount:1});
      }
      if (config.clickRate>0 && config.inputBatchMilliseconds>0) {
        const end=Math.min(t+config.inputBatchMilliseconds,m.nextPurchase,t+(observation.decisionHorizonMs??1000));
        if(end>t && m.nextClick<=end) {
          const inputs=[];let at=t;
          while(m.nextClick<=end) {
            if(m.nextClick>at) inputs.push({type:'wait',milliseconds:m.nextClick-at});
            at=Math.max(at,m.nextClick);inputs.push({type:'click'});m.nextClick=at+1000/config.clickRate;
          }
          if(end>at) inputs.push({type:'wait',milliseconds:end-at});
          return answer({type:'sequence',actions:inputs});
        }
      }
      const wait = Math.min(1000, Math.max(1,m.nextPurchase-t), config.clickRate > 0 ? Math.max(1,m.nextClick-t) : 1000);
      return answer({type:'wait',milliseconds:wait});
    };
  })());
    const earlyGrow = ((function () {
    const config = {"clickRate":50,"purchaseRule":"exchange","upgradeShare":0.5,"inputBatchMilliseconds":1000,"purchaseIntervalMilliseconds":1000};
    return function (observation, actions, memory) {
      const m = memory ? { ...memory } : { nextClick: 100, nextPurchase: 0 };
      const t = observation.elapsedMs;
      const answer = action => ({ action, memory: m });
      if (observation.progression.onAscend || observation.progression.ascendTimer || observation.progression.reincarnateTimer) return answer({type:'wait',milliseconds:100});
      const shimmer = observation.shimmers[0];
      if (shimmer) return answer({type:'click-shimmer',id:shimmer.id});
      if (config.clickRate > 0 && t >= m.nextClick) {
        m.nextClick = t + 1000 / config.clickRate;
        return answer({type:'click'});
      }
      if (t >= m.nextPurchase) {
        m.nextPurchase = t + config.purchaseIntervalMilliseconds;
        const upgrade = observation.shop.upgrades
          .filter(u => u.pool !== 'toggle' && u.pool !== 'prestige' && u.canBuy && u.price <= observation.cookies * config.upgradeShare)
          .sort((a,b) => a.price-b.price || a.id-b.id)[0];
        if (upgrade) return answer({type:'buy-upgrade',id:upgrade.id});
        const buildings = observation.shop.buildings.filter(b => !b.locked && b.storedCps > 0);
        const totalBase = observation.shop.buildings.reduce((sum,b) => sum+b.storedTotalCps,0);
        const multiplier = totalBase > 0 ? observation.cookiesPs / totalBase : 1;
        const income = Math.max(observation.cookiesPs,0.1);
        const score = b => config.purchaseRule === 'cheapest' ? b.buy1price
          : config.purchaseRule === 'roi' ? b.buy1price / Math.max(b.storedCps*multiplier,0.000001)
          : Math.max(b.buy1price-observation.cookies,0)/income + b.buy1price/Math.max(b.storedCps*multiplier,0.000001);
        buildings.sort((a,b) => score(a)-score(b) || a.id-b.id);
        const best = buildings[0];
        if (best && best.buy1price <= observation.cookies) return answer({type:'buy-building',id:best.id,amount:1});
      }
      if (config.clickRate>0 && config.inputBatchMilliseconds>0) {
        const end=Math.min(t+config.inputBatchMilliseconds,m.nextPurchase,t+(observation.decisionHorizonMs??1000));
        if(end>t && m.nextClick<=end) {
          const inputs=[];let at=t;
          while(m.nextClick<=end) {
            if(m.nextClick>at) inputs.push({type:'wait',milliseconds:m.nextClick-at});
            at=Math.max(at,m.nextClick);inputs.push({type:'click'});m.nextClick=at+1000/config.clickRate;
          }
          if(end>at) inputs.push({type:'wait',milliseconds:end-at});
          return answer({type:'sequence',actions:inputs});
        }
      }
      const wait = Math.min(1000, Math.max(1,m.nextPurchase-t), config.clickRate > 0 ? Math.max(1,m.nextClick-t) : 1000);
      return answer({type:'wait',milliseconds:wait});
    };
  })());
    const earlyNoClick = ((function () {
    const config = {"clickRate":0,"purchaseRule":"exchange","upgradeShare":0.5,"inputBatchMilliseconds":0,"purchaseIntervalMilliseconds":1000};
    return function (observation, actions, memory) {
      const m = memory ? { ...memory } : { nextClick: 100, nextPurchase: 0 };
      const t = observation.elapsedMs;
      const answer = action => ({ action, memory: m });
      if (observation.progression.onAscend || observation.progression.ascendTimer || observation.progression.reincarnateTimer) return answer({type:'wait',milliseconds:100});
      const shimmer = observation.shimmers[0];
      if (shimmer) return answer({type:'click-shimmer',id:shimmer.id});
      if (config.clickRate > 0 && t >= m.nextClick) {
        m.nextClick = t + 1000 / config.clickRate;
        return answer({type:'click'});
      }
      if (t >= m.nextPurchase) {
        m.nextPurchase = t + config.purchaseIntervalMilliseconds;
        const upgrade = observation.shop.upgrades
          .filter(u => u.pool !== 'toggle' && u.pool !== 'prestige' && u.canBuy && u.price <= observation.cookies * config.upgradeShare)
          .sort((a,b) => a.price-b.price || a.id-b.id)[0];
        if (upgrade) return answer({type:'buy-upgrade',id:upgrade.id});
        const buildings = observation.shop.buildings.filter(b => !b.locked && b.storedCps > 0);
        const totalBase = observation.shop.buildings.reduce((sum,b) => sum+b.storedTotalCps,0);
        const multiplier = totalBase > 0 ? observation.cookiesPs / totalBase : 1;
        const income = Math.max(observation.cookiesPs,0.1);
        const score = b => config.purchaseRule === 'cheapest' ? b.buy1price
          : config.purchaseRule === 'roi' ? b.buy1price / Math.max(b.storedCps*multiplier,0.000001)
          : Math.max(b.buy1price-observation.cookies,0)/income + b.buy1price/Math.max(b.storedCps*multiplier,0.000001);
        buildings.sort((a,b) => score(a)-score(b) || a.id-b.id);
        const best = buildings[0];
        if (best && best.buy1price <= observation.cookies) return answer({type:'buy-building',id:best.id,amount:1});
      }
      if (config.clickRate>0 && config.inputBatchMilliseconds>0) {
        const end=Math.min(t+config.inputBatchMilliseconds,m.nextPurchase,t+(observation.decisionHorizonMs??1000));
        if(end>t && m.nextClick<=end) {
          const inputs=[];let at=t;
          while(m.nextClick<=end) {
            if(m.nextClick>at) inputs.push({type:'wait',milliseconds:m.nextClick-at});
            at=Math.max(at,m.nextClick);inputs.push({type:'click'});m.nextClick=at+1000/config.clickRate;
          }
          if(end>at) inputs.push({type:'wait',milliseconds:end-at});
          return answer({type:'sequence',actions:inputs});
        }
      }
      const wait = Math.min(1000, Math.max(1,m.nextPurchase-t), config.clickRate > 0 ? Math.max(1,m.nextClick-t) : 1000);
      return answer({type:'wait',milliseconds:wait});
    };
  })());
    const growSingle = ((function () {
    const config = {"clickRate":50,"purchaseRule":"exchange","upgradeShare":0.5,"inputBatchMilliseconds":0,"purchaseIntervalMilliseconds":300};
    return function (observation, actions, memory) {
      const m = memory ? { ...memory } : { nextClick: 100, nextPurchase: 0 };
      const t = observation.elapsedMs;
      const answer = action => ({ action, memory: m });
      if (observation.progression.onAscend || observation.progression.ascendTimer || observation.progression.reincarnateTimer) return answer({type:'wait',milliseconds:100});
      const shimmer = observation.shimmers[0];
      if (shimmer) return answer({type:'click-shimmer',id:shimmer.id});
      if (config.clickRate > 0 && t >= m.nextClick) {
        m.nextClick = t + 1000 / config.clickRate;
        return answer({type:'click'});
      }
      if (t >= m.nextPurchase) {
        m.nextPurchase = t + config.purchaseIntervalMilliseconds;
        const upgrade = observation.shop.upgrades
          .filter(u => u.pool !== 'toggle' && u.pool !== 'prestige' && u.canBuy && u.price <= observation.cookies * config.upgradeShare)
          .sort((a,b) => a.price-b.price || a.id-b.id)[0];
        if (upgrade) return answer({type:'buy-upgrade',id:upgrade.id});
        const buildings = observation.shop.buildings.filter(b => !b.locked && b.storedCps > 0);
        const totalBase = observation.shop.buildings.reduce((sum,b) => sum+b.storedTotalCps,0);
        const multiplier = totalBase > 0 ? observation.cookiesPs / totalBase : 1;
        const income = Math.max(observation.cookiesPs,0.1);
        const score = b => config.purchaseRule === 'cheapest' ? b.buy1price
          : config.purchaseRule === 'roi' ? b.buy1price / Math.max(b.storedCps*multiplier,0.000001)
          : Math.max(b.buy1price-observation.cookies,0)/income + b.buy1price/Math.max(b.storedCps*multiplier,0.000001);
        buildings.sort((a,b) => score(a)-score(b) || a.id-b.id);
        const best = buildings[0];
        if (best && best.buy1price <= observation.cookies) return answer({type:'buy-building',id:best.id,amount:1});
      }
      if (config.clickRate>0 && config.inputBatchMilliseconds>0) {
        const end=Math.min(t+config.inputBatchMilliseconds,m.nextPurchase,t+(observation.decisionHorizonMs??1000));
        if(end>t && m.nextClick<=end) {
          const inputs=[];let at=t;
          while(m.nextClick<=end) {
            if(m.nextClick>at) inputs.push({type:'wait',milliseconds:m.nextClick-at});
            at=Math.max(at,m.nextClick);inputs.push({type:'click'});m.nextClick=at+1000/config.clickRate;
          }
          if(end>at) inputs.push({type:'wait',milliseconds:end-at});
          return answer({type:'sequence',actions:inputs});
        }
      }
      const wait = Math.min(1000, Math.max(1,m.nextPurchase-t), config.clickRate > 0 ? Math.max(1,m.nextClick-t) : 1000);
      return answer({type:'wait',milliseconds:wait});
    };
  })());
    const growWithoutClicks = ((function () {
    const config = {"clickRate":0,"purchaseRule":"exchange","upgradeShare":0.5,"inputBatchMilliseconds":0,"purchaseIntervalMilliseconds":300};
    return function (observation, actions, memory) {
      const m = memory ? { ...memory } : { nextClick: 100, nextPurchase: 0 };
      const t = observation.elapsedMs;
      const answer = action => ({ action, memory: m });
      if (observation.progression.onAscend || observation.progression.ascendTimer || observation.progression.reincarnateTimer) return answer({type:'wait',milliseconds:100});
      const shimmer = observation.shimmers[0];
      if (shimmer) return answer({type:'click-shimmer',id:shimmer.id});
      if (config.clickRate > 0 && t >= m.nextClick) {
        m.nextClick = t + 1000 / config.clickRate;
        return answer({type:'click'});
      }
      if (t >= m.nextPurchase) {
        m.nextPurchase = t + config.purchaseIntervalMilliseconds;
        const upgrade = observation.shop.upgrades
          .filter(u => u.pool !== 'toggle' && u.pool !== 'prestige' && u.canBuy && u.price <= observation.cookies * config.upgradeShare)
          .sort((a,b) => a.price-b.price || a.id-b.id)[0];
        if (upgrade) return answer({type:'buy-upgrade',id:upgrade.id});
        const buildings = observation.shop.buildings.filter(b => !b.locked && b.storedCps > 0);
        const totalBase = observation.shop.buildings.reduce((sum,b) => sum+b.storedTotalCps,0);
        const multiplier = totalBase > 0 ? observation.cookiesPs / totalBase : 1;
        const income = Math.max(observation.cookiesPs,0.1);
        const score = b => config.purchaseRule === 'cheapest' ? b.buy1price
          : config.purchaseRule === 'roi' ? b.buy1price / Math.max(b.storedCps*multiplier,0.000001)
          : Math.max(b.buy1price-observation.cookies,0)/income + b.buy1price/Math.max(b.storedCps*multiplier,0.000001);
        buildings.sort((a,b) => score(a)-score(b) || a.id-b.id);
        const best = buildings[0];
        if (best && best.buy1price <= observation.cookies) return answer({type:'buy-building',id:best.id,amount:1});
      }
      if (config.clickRate>0 && config.inputBatchMilliseconds>0) {
        const end=Math.min(t+config.inputBatchMilliseconds,m.nextPurchase,t+(observation.decisionHorizonMs??1000));
        if(end>t && m.nextClick<=end) {
          const inputs=[];let at=t;
          while(m.nextClick<=end) {
            if(m.nextClick>at) inputs.push({type:'wait',milliseconds:m.nextClick-at});
            at=Math.max(at,m.nextClick);inputs.push({type:'click'});m.nextClick=at+1000/config.clickRate;
          }
          if(end>at) inputs.push({type:'wait',milliseconds:end-at});
          return answer({type:'sequence',actions:inputs});
        }
      }
      const wait = Math.min(1000, Math.max(1,m.nextPurchase-t), config.clickRate > 0 ? Math.max(1,m.nextClick-t) : 1000);
      return answer({type:'wait',milliseconds:wait});
    };
  })());
    const tend = ((function(observation, availableActions, memory) {
    const decision = function gardenDecision(observation, availableActions, memory, recipes, dropCrops, cookiePlot) {
  memory ||= {};
  const config = { farmDrops: true, harvestTarget: 1000, requireFullPlot: true,
    boostNovelGrowth: true, novelGrowthMaxCostFraction: 0.01, naturalCookieFarm: false,
    sacrificesRequired: 1, maxWaitMs: 1000, ...(memory.config || {}) };
  const nextMemory = { ...memory, config };
  const G = observation.garden;
  const result = (status, goal, reason, action = null, extra = {}) =>
    ({ status, goal, reason, action, memory: nextMemory, ...extra });
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
};
    return decision(observation, availableActions, {...(memory || {}), config: {...{}, ...((memory || {}).config || {})}},
      [{"target":"meddleweed","kind":"spontaneous","parents":{}},{"target":"brownMold","kind":"uproot","parents":{"meddleweed":1}},{"target":"crumbspore","kind":"uproot","parents":{"meddleweed":1}},{"target":"thumbcorn","parents":{"bakerWheat":2},"candidateProbability":0.05},{"target":"cronerice","parents":{"bakerWheat":1,"thumbcorn":1},"candidateProbability":0.01},{"target":"gildmillet","parents":{"cronerice":1,"thumbcorn":1},"candidateProbability":0.03},{"target":"clover","parents":{"bakerWheat":1,"gildmillet":1},"candidateProbability":0.03},{"target":"shimmerlily","parents":{"clover":1,"gildmillet":1},"candidateProbability":0.02},{"target":"elderwort","parents":{"shimmerlily":1,"cronerice":1},"candidateProbability":0.01},{"target":"ichorpuff","parents":{"elderwort":1,"crumbspore":1},"candidateProbability":0.002},{"target":"bakeberry","parents":{"bakerWheat":2},"candidateProbability":0.001},{"target":"chocoroot","parents":{"bakerWheat":1,"brownMold":1},"candidateProbability":0.1,"immatureParents":["brownMold"]},{"target":"whiteMildew","parents":{"brownMold":1},"candidateProbability":0.5},{"target":"whiteChocoroot","parents":{"chocoroot":1,"whiteMildew":1},"candidateProbability":0.1,"immatureParents":["whiteMildew"]},{"target":"whiskerbloom","parents":{"shimmerlily":1,"whiteChocoroot":1},"candidateProbability":0.01},{"target":"chimerose","parents":{"shimmerlily":1,"whiskerbloom":1},"candidateProbability":0.05},{"target":"nursetulip","parents":{"whiskerbloom":2},"candidateProbability":0.05},{"target":"greenRot","parents":{"whiteMildew":1,"clover":1},"candidateProbability":0.05},{"target":"keenmoss","parents":{"greenRot":1,"brownMold":1},"candidateProbability":0.1},{"target":"drowsyfern","parents":{"chocoroot":1,"keenmoss":1},"candidateProbability":0.005},{"target":"wardlichen","parents":{"cronerice":1,"whiteMildew":1},"candidateProbability":0.005},{"target":"queenbeet","parents":{"chocoroot":1,"bakeberry":1},"candidateProbability":0.01},{"target":"queenbeetLump","parents":{"queenbeet":8},"candidateProbability":0.001},{"target":"duketater","parents":{"queenbeet":2},"candidateProbability":0.001},{"target":"doughshroom","parents":{"crumbspore":2},"candidateProbability":0.005},{"target":"glovemorel","parents":{"crumbspore":1,"thumbcorn":1},"candidateProbability":0.02},{"target":"cheapcap","parents":{"crumbspore":1,"shimmerlily":1},"candidateProbability":0.04},{"target":"foolBolete","parents":{"doughshroom":1,"greenRot":1},"candidateProbability":0.04},{"target":"wrinklegill","parents":{"crumbspore":1,"brownMold":1},"candidateProbability":0.06},{"target":"shriekbulb","parents":{"duketater":3},"candidateProbability":0.005,"immatureParents":["duketater"]},{"target":"tidygrass","parents":{"bakerWheat":1,"whiteChocoroot":1},"candidateProbability":0.002},{"target":"everdaisy","parents":{"tidygrass":3,"elderwort":3},"candidateProbability":0.002},{"target":"goldenClover","parents":{"bakerWheat":1,"gildmillet":1},"candidateProbability":0.0007}], [{"upgrade":"Ichor syrup","crop":"ichorpuff","rate":0.005},{"upgrade":"Wheat slims","crop":"bakerWheat","rate":0.001},{"upgrade":"Elderwort biscuits","crop":"elderwort","rate":0.01},{"upgrade":"Bakeberry cookies","crop":"bakeberry","rate":0.015},{"upgrade":"Fern tea","crop":"drowsyfern","rate":0.01},{"upgrade":"Duketater cookies","crop":"duketater","rate":0.005},{"upgrade":"Green yeast digestives","crop":"greenRot","rate":0.005}], [["goldenClover","goldenClover","goldenClover","goldenClover","goldenClover","goldenClover"],["nursetulip","nursetulip","nursetulip","nursetulip","nursetulip","nursetulip"],["goldenClover","goldenClover","goldenClover","goldenClover","goldenClover","goldenClover"],["nursetulip","nursetulip","nursetulip","nursetulip","nursetulip","nursetulip"],["goldenClover","goldenClover","goldenClover","goldenClover","goldenClover","goldenClover"],["nursetulip","nursetulip","nursetulip","nursetulip","nursetulip","nursetulip"]]);
  }));
    const trade = ((function(observation, availableActions, memory) {
    const decision = function marketDecision(observation, availableActions, memory, achievements, requiredHighest) {
  memory ||= {};
  const config = { brokerTarget: 50, buyFactor: 0.65, sellFactor: 1.05,
    maxWaitMs: 1000, maxDecisions: null, prepareDebtEvasion: false, collectTrades: true, ...(memory.config || {}) };
  // A policy must remain available on long random waiting paths. Finite caps
  // are opt-in diagnostics; the evaluator owns the experiment's work budget.
  const nextMemory = { ...memory, config,
    decisions: config.maxDecisions === null ? null : (memory.decisions || 0) + 1 };
  const result = (status, goal, reason, action = null, extra = {}) =>
    ({ status, goal, reason, action, memory: nextMemory, ...extra });
  if (!Number.isSafeInteger(config.brokerTarget) || config.brokerTarget < 0 || config.brokerTarget > 500
    || !(config.buyFactor > 0 && config.sellFactor > config.buyFactor * 1.2)
    || !Number.isFinite(config.sellFactor) || typeof config.collectTrades !== 'boolean' || !(config.maxWaitMs > 0 && Number.isFinite(config.maxWaitMs))
    || config.maxDecisions !== null && (!Number.isSafeInteger(config.maxDecisions) || config.maxDecisions < 1)) {
    return result('blocked', 'Market configuration', 'Use finite limits and a sale threshold above the maximum purchase overhead.');
  }
  if (config.maxDecisions !== null && nextMemory.decisions > config.maxDecisions) return result('budget-exhausted', 'Market controller', 'The configured diagnostic decision limit was reached.');
  const M = observation.market;
  if (!M?.ready) return result('needs-resources', 'Stock Market access', 'Bank level 1 and the loaded Stock Market are required.', null, { building: 'Bank', level: 1 });
  if (observation.progression?.onAscend || observation.progression?.ascensionMode !== 0
    || observation.progression?.ascendTimer > 0 || observation.progression?.reincarnateTimer > 0) {
    return result('blocked', 'Active Stock Market', 'The controller requires an active normal run.');
  }
  if (observation.controls?.promptOn) return result('blocked', 'Market control', 'Resolve the current unrelated prompt first.');
  if (M.goods?.length !== 18 || new Set(M.goods.map(g => g.id)).size !== 18
    || M.goods.some(g => !Number.isInteger(g.id) || g.id < 0 || g.id > 17
      || !(g.price > 0 && Number.isFinite(g.price)) || !(g.stock >= 0 && Number.isSafeInteger(g.stock))
      || !(g.maxStock >= 0 && Number.isSafeInteger(g.maxStock))
      || !(g.buyCookiePrice > 0 && Number.isFinite(g.buyCookiePrice)))) {
    return result('blocked', 'Pinned market catalogue', 'The observed prices, storage, or goods do not match the supported market.');
  }
  const won = name => !!observation.achievements?.[name];
  const missing = achievements.filter(name => !won(name));
  // A closed panel needs opening only when this controller will use it.
  // Completed market work must not delay unrelated completion purchases.
  if (!missing.length && M.officeLevel === 5 && (!config.prepareDebtEvasion || won('Debt evasion'))) {
    return result('complete', 'Market trading and offices', 'All eight trading and office achievements are won, and the current office is fully upgraded.');
  }
  if (!config.collectTrades && M.officeLevel >= 2) return result('prepared', 'Loan access',
    'The first loan is unlocked. Defer further market purchases until the final collection run.');
  if (M.open === false) return result('acting', 'Market control', 'Open the native market panel before its controls are used.', { type: 'minigame-open', id: M.buildingId ?? 5 });
  const wait = (goal, reason) => result('waiting', goal, reason, { type: 'wait',
    milliseconds: Math.max(1, Math.min(config.maxWaitMs, M.nextTickMs > 0 ? M.nextTickMs : 1000 / 30)) },
  { wakeAfterMs: M.nextTickMs });
  const buy = (good, amount, goal, reason) => result('acting', goal, reason,
    { type: 'market-buy', id: good.id, amount });
  const sell = (good, goal, reason) => result('acting', goal, reason,
    { type: 'market-sell', id: good.id, amount: 10000 }); // Native All sentinel.
  const canBuy = good => good.active && good.visible !== false && good.canBuy !== false;
  const canSell = good => good.active && good.visible !== false && good.canSell !== false && good.stock > 0;
  const enoughCookies = (good, n) => observation.cookies >= good.buyCookiePrice * n;
  const exactBuyFits = (good, n) => n > 0 && n < 10000 && canBuy(good)
    && good.stock + n <= good.maxStock && enoughCookies(good, n);
  // Guard against a rounded-down product at the native >= 86400 boundary.
  const dayUnits = price => { const n = Math.ceil(86400 / price); return price * n >= 86400 ? n : n + 1; };
  const goods = [...M.goods].sort((a, b) => b.price - a.price || a.id - b.id);
  const storageRequest = (good, capacity) => {
    const buildingId = good.buildingId ?? good.id + 2;
    const building = observation.shop?.buildings?.find(b => b.id === buildingId);
    const level = building?.level ?? good.buildingLevel ?? 0;
    // One highest-owned building is also needed to unlock the good, even if
    // office and level bonuses alone provide the requested storage capacity.
    const highest = Math.max(1, requiredHighest(capacity, M.officeLevel, level));
    return { good: good.id, buildingId, ...(building ? { building: building.name } : {}),
      amount: highest, requiredCapacity: capacity, requiredBuildingHighest: highest };
  };

  let officeNeed = null;
  // The second office unlocks the first loan. Further offices, brokers and
  // holdings are lost on ascension, so the composed controller can defer them.
  const officeTarget = config.collectTrades ? 5 : 2;
  if (M.officeLevel < officeTarget) {
    const office = M.offices?.[M.officeLevel];
    if (!office || !(office.cursorAmount > 0 && office.cursorLevel > 0)) return result('blocked', 'Market offices', 'The next office cost is absent.');
    const cursorLevel = observation.progression?.buildingLevels?.Cursor || 0;
    const cursorAmount = observation.progression?.buildingAmounts?.Cursor || 0;
    if (cursorLevel >= office.cursorLevel && cursorAmount >= office.cursorAmount) {
      if (M.officeUpgradeVisible === false) return wait('Market offices', 'Wait for the native office control to become visible.');
      return result('acting', config.collectTrades ? 'Pyramid scheme' : 'Loan access', 'Sacrifice the required cursors to upgrade the office.', { type: 'market-office' });
    }
    officeNeed = cursorLevel < office.cursorLevel
      ? result('needs-level', 'Market offices', 'The next office requires a higher Cursor level.', null, { building: 'Cursor', level: office.cursorLevel })
      : result('needs-resources', 'Market offices', 'The next office requires more current cursors.', null, { building: 'Cursor', amount: office.cursorAmount });
  }

  if (!config.collectTrades) return officeNeed || result('prepared', 'Loan access',
    'The first loan is unlocked. Defer further market purchases until the final collection run.');

  if (!missing.length && M.officeLevel === 5) {
    if (config.prepareDebtEvasion && !won('Debt evasion')) {
      if (M.loans?.some(loan => loan.activeFrames > 0)) {
        return result('needs-ascension', 'Debt evasion', 'Ascend before the active loan enters its interest period. Coordinate this with the other run goals.');
      }
      const loan = M.loans?.find(loan => loan.unlocked && !loan.activeFrames && !loan.interestFrames);
      if (!loan) return wait('Debt evasion', 'Wait for a loan to leave its interest period.');
      if (loan.visible === false) return wait('Debt evasion', 'Wait for the native loan control to become visible.');
      return result('acting', 'Debt evasion', 'Start an available loan for the planned ascension.', { type: 'market-loan', id: loan.id });
    }
    return result('complete', 'Market trading and offices', 'All eight trading and office achievements are won, and the current office is fully upgraded.');
  }

  // Brokers cost cookies but do not subtract from the displayed market profit.
  if (!won('Liquid assets') && M.brokers < Math.min(config.brokerTarget, M.maxBrokers)
    && M.brokerVisible !== false && Number.isFinite(M.brokerPrice) && observation.cookies >= M.brokerPrice) {
    return result('acting', 'Trading overhead', 'Hire a broker within the configured limit.', { type: 'market-broker' });
  }

  if (!won('Buy buy buy')) {
    for (const good of goods) {
      const n = dayUnits(good.price * M.overheadMultiplier);
      if (exactBuyFits(good, n)) return buy(good, n, 'Buy buy buy', 'Buy at least 86400 market dollars of stock in one transaction.');
    }
  }

  // Keep these holdings together until the native all-goods checks award them.
  if (!won('No nobility in poverty') || !won('Rookie numbers')) {
    const deficient = goods.filter(good => good.stock < 500);
    for (const good of deficient) {
      if (exactBuyFits(good, 500 - good.stock)) return buy(good, 500 - good.stock, 'No nobility in poverty', 'Bring this holding to 500 units without selling the other holdings.');
    }
    if (!deficient.length) {
      const trigger = goods.find(good => exactBuyFits(good, 1));
      if (trigger) return buy(trigger, 1, 'No nobility in poverty', 'Let the native purchase callback check all holdings.');
    }
    const locked = deficient.find(good => !good.active || good.maxStock < 500);
    if (locked) return officeNeed || result('needs-resources', 'Market warehouses', 'This good must be unlocked with storage for 500 units.', null,
      storageRequest(locked, 500));
    const unaffordable = deficient.find(good => !enoughCookies(good, 500 - good.stock));
    if (unaffordable) return result('needs-resources', 'No nobility in poverty', 'The next holding requires more cookies.', null,
      { requiredCookies: unaffordable.buyCookiePrice * (500 - unaffordable.stock), good: unaffordable.id });
    return wait('No nobility in poverty', 'Wait for the restriction on buying after a sale to end.');
  }

  if (!won('Full warehouses')) {
    const good = goods.find(g => exactBuyFits(g, Math.max(1, 1000 - g.stock)));
    if (good) return buy(good, Math.max(1, 1000 - good.stock), 'Full warehouses', 'Hold at least 1000 units of one stock.');
    if (!goods.some(g => g.active && g.maxStock >= 1000)) {
      // Choose the cheapest next building. This ensures an explicit resource
      // request; it does not claim to minimize the full acquisition cost.
      const candidate = [...goods].sort((a, b) => {
        const price = g => observation.shop?.buildings?.find(x => x.id === (g.buildingId ?? g.id + 2))?.buy1price ?? Infinity;
        return price(a) - price(b) || a.id - b.id;
      })[0];
      return officeNeed || result('needs-resources', 'Full warehouses', 'At least one good requires storage for 1000 units.', null, storageRequest(candidate, 1000));
    }
    const fill = goods.filter(g => canBuy(g) && g.maxStock >= 1000 && g.stock < 1000)
      .sort((a,b) => a.buyCookiePrice * (1000-a.stock) - b.buyCookiePrice * (1000-b.stock) || a.id-b.id)[0];
    if (fill) return result('needs-resources', 'Full warehouses', 'Reserve the cookies needed to fill one warehouse to 1000 units.', null,
      { good: fill.id, requiredCookies: fill.buyCookiePrice * (1000-fill.stock) });
    return wait('Full warehouses', 'Wait for the restriction on buying after a sale to end.');
  }

  if (!won('Make my day')) {
    const sale = goods.find(g => canSell(g) && g.price * g.stock >= 86400);
    if (sale) return sell(sale, 'Make my day', 'Sell at least 86400 market dollars of stock in one transaction.');
    // One startup trade may lose overhead. Later threshold trades recover it.
    const purchase = goods.find(g => exactBuyFits(g, dayUnits(g.price) - g.stock));
    if (purchase) return buy(purchase, dayUnits(purchase.price) - purchase.stock, 'Make my day', 'Build a holding large enough for the required single sale.');
    // Selling below the achievement threshold could repeat a losing startup
    // trade forever. Keep these holdings until one sale can win the goal.
    // Each good can receive at most its finite storage capacity before then.
    return wait('Make my day', 'Keep the startup holdings until one sale is worth at least 86400 market dollars.');
  }

  // The fixed thresholds use only a displayed price and the known Bank level.
  // A new round trip buys at <= 0.65*r, including <=20% overhead, and sells at
  // >= 1.05*r. This is a positive margin, not a bound on the waiting time.
  for (const good of goods) {
    const resting = 10 + 10 * good.id + M.bankLevel - 1;
    if (canSell(good) && good.price >= config.sellFactor * resting) return sell(good, 'Liquid assets', 'Sell above the fixed sale threshold.');
  }
  if (!won('Liquid assets')) {
    for (const good of goods) {
      const resting = 10 + 10 * good.id + M.bankLevel - 1;
      if (canBuy(good) && good.stock < good.maxStock && good.price <= config.buyFactor * resting
        && enoughCookies(good, 1)) {
        return buy(good, 10000, 'Liquid assets', 'Use native Max to buy below the fixed purchase threshold.');
      }
    }
  }
  if (officeNeed) return officeNeed;
  return wait(missing[0] || 'Market goals', 'Wait for the next visible market prices or trade permission.');
};
    return decision(observation, availableActions, {...(memory || {}), config: {...{}, ...((memory || {}).config || {})}},
      ["Initial public offering","Rookie numbers","No nobility in poverty","Full warehouses","Make my day","Buy buy buy","Pyramid scheme","Liquid assets"], function requiredMarketBuildingHighest(capacity, officeLevel, buildingLevel) {
  if (!Number.isSafeInteger(capacity) || capacity < 0 || !Number.isInteger(officeLevel) || officeLevel < 0 || officeLevel > 5
    || !Number.isSafeInteger(buildingLevel) || buildingLevel < 0) throw new Error('Invalid market storage requirement');
  const bonus = [0, 25, 75, 150, 250, 250][officeLevel];
  const factor = officeLevel === 5 ? 1.5 : 1;
  let highest = Math.max(0, Math.floor((capacity - bonus - buildingLevel * 10 - 1) / factor) + 1);
  const nativeCapacity = amount => Math.ceil(amount * factor + bonus + buildingLevel * 10);
  // Preserve the native binary64 boundary if a large integer quote rounds.
  while (nativeCapacity(highest) < capacity) highest++;
  while (highest > 0 && nativeCapacity(highest - 1) >= capacity) highest--;
  return highest;
});
  }));
    const collectMisc = ((function () { const MISC_ACHIEVEMENTS_INTERNAL = ["Cookie-dunker","Just wrong","Early bird","Fading luck","Thick-skinned","No time like the present"]; return (function miscDecision(o, actions, memory) {
  const m = { ...(memory || {}) };
  let timing = { deferShimmerIds: [], wakeAfterMs: 1000 };
  const result = (status, goal, action = null, extra = {}) => ({ status, goal, action, memory: m, ...timing, ...extra });
  const act = (goal, action) => result('acting', goal, action);
  const resources = (goal, requiredCookies) => result('needs-resources', goal, null, { requiredCookies });
  const won = name => !!o.achievements[name];
  if (o.progression.onAscend || o.progression.ascendTimer || o.progression.reincarnateTimer) return result('blocked', 'Active run');

  // The send result is a code displayed by the native prompt, not save data.
  if (m.giftPending) {
    delete m.giftPending;
    if (o.controls.promptOn && o.giftCode) {
      m.giftCode = o.giftCode;
      return act('No time like the present', { type: 'close-prompt' });
    }
  }
  if (o.controls.promptOn) return result('blocked', 'Unrelated prompt');

  if (m.dunkViewport && won('Cookie-dunker')) {
    delete m.dunkViewport;
    return act('Restore viewport', { type: 'resize', width: 1200, height: 900 });
  }
  if (!won('Cookie-dunker') && Object.values(o.achievements).filter(Boolean).length >= 3) {
    if (!m.dunkViewport) {
      m.dunkViewport = true;
      return act('Cookie-dunker', { type: 'resize', width: 1200, height: 200 });
    }
  }
  // During the no-upgrade challenge the scheduler can preserve this income.
  // The required sale remains available immediately after Hardcore is won.
  if (!won('Just wrong') && o.progression.buildingAmounts.Grandma > 0
    && (!m.deferGrandmaSaleUntilHardcore || won('Hardcore'))) {
    return act('Just wrong', { type: 'sell-building', id: 1, amount: 1 });
  }

  // A golden cookie's remaining lifetime is measured in engine frames.
  // No hidden effect or random seed is inspected. A forced cookie may not
  // award these goals; the same rule will try a later natural spawn.
  const golden = o.shimmers.filter(s => s.type === 'golden');
  if (!won('Early bird') && golden.length) return act('Early bird', { type: 'click-shimmer', id: golden[0].id });
  let deferred = [];
  let wakeAfterMs = 1000;
  if (!won('Fading luck') && golden.length) {
    const target = golden.find(s => s.id === m.fadingId) || golden.reduce((a, b) => a.life < b.life ? a : b);
    m.fadingId = target.id;
    const fps = o.fps || 30;
    if (target.life < fps) return act('Fading luck', { type: 'click-shimmer', id: target.id });
    deferred = [target.id];
    wakeAfterMs = Math.max(1, (target.life - (fps - 1)) * 1000 / fps);
  } else delete m.fadingId;
  const extra = { deferShimmerIds: deferred, wakeAfterMs };
  timing = extra;

  if (m.restoreGoldenSwitch) {
    const restore = o.shop.upgrades.find(u => u.name === 'Golden switch [on]');
    if (restore?.canBuy && o.cookies >= restore.price) { delete m.restoreGoldenSwitch; return act('Restore golden-cookie spawns', { type: 'buy-upgrade', id: restore.id }); }
    if (!o.upgrades['Golden switch [off]']?.bought) delete m.restoreGoldenSwitch;
    else if (restore) return resources('Restore golden-cookie spawns', restore.price);
    else return result('needs-unlock', 'Restore golden-cookie spawns');
  }

  if (!won('No time like the present') && o.upgrades['Wrapping paper']?.bought
      && o.progression.ascensionMode === 0 && !o.buffs['Gifted out']) {
    if (o.cookies < 1e9) return resources('No time like the present', 1e9);
    if (m.giftCode) return act('No time like the present', { type: 'gift-redeem', code: m.giftCode });
    m.giftPending = true;
    return act('No time like the present', { type: 'gift-send', amount: 1, message: 'Completion gift' });
  }
  if (!won('Thick-skinned') && o.upgrades['Reinforced membrane']?.bought && won('Neverclick') && won('Hardcore')) {
    const restore = o.shop.upgrades.find(u => u.name === 'Shimmering veil [off]');
    if (restore?.canBuy && o.cookies >= restore.price) return act('Thick-skinned', { type: 'buy-upgrade', id: restore.id });
    if (restore) return resources('Thick-skinned', restore.price);
    if (o.upgrades['Shimmering veil [off]']?.bought && o.elapsedMs >= (m.veilClickAfter || 100)) {
      m.veilClickAfter = o.elapsedMs + 20;
      return act('Thick-skinned', { type: 'click' });
    }
  }
  const accessed = name => o.upgrades[name]?.unlocked || o.upgrades[name]?.bought || o.history.accessedUpgrades.includes(name);
  if (won('Black cat\'s paw') && !accessed('Golden switch [on]')) {
    const enable = o.shop.upgrades.find(u => u.name === 'Golden switch [off]');
    // This is a conservative reserve for the two native toggle prices. The
    // final bank can pay it without a period of disabled golden-cookie spawns.
    if (enable?.canBuy && o.cookies >= enable.price * 100) {
      m.restoreGoldenSwitch = true;
      return act('Golden switch access', { type: 'buy-upgrade', id: enable.id });
    }
    if (enable) return resources('Golden switch access', enable.price * 100);
  }
  return result(MISC_ACHIEVEMENTS_INTERNAL.every(won) && accessed('Golden switch [on]') && !m.restoreGoldenSwitch ? 'complete' : 'waiting', 'Miscellaneous goals', null, extra);
}); })());
    const collectSeason = ((function(observation, availableActions, memory) {
    return (function seasonDecision(o, actions, memory, researchNames, dragonDrops) {
  const config = { seasons: ['valentines', 'christmas', 'halloween', 'easter'],
    preserveChallengeAchievements: true, research: true, fortunes: true, dragonDrops: true, wrinklers: true,
    helperGrandma: true, eldeer: true, reindeerTarget: 200, pledgeTarget: 10,
    maxSeasonUses: 12, helperMaxWidth: 16384,
    maxWaitMs: 1000, petIntervalMs: 0, suppressWrathForCookieCount: false, ...(memory?.config || {}) };
  const m = { ...(memory || {}), config };
  const answer = (status, goal, reason, action = null, extra = {}) => ({ status, goal, reason, action, memory: m, ...extra });
  const now = o.wallTimeMs;
  const wait = (goal, reason, ms = config.maxWaitMs) => answer('waiting', goal, reason,
    { type: 'wait', milliseconds: Math.max(1, Math.min(config.maxWaitMs, ms)) }, { wakeAfterMs: ms });
  const act = (goal, reason, action) => answer('acting', goal, reason, action);
  const retry = (goal, reason, retryReason) => answer('needs-ascension', goal, reason, null,
    { retryReason, requiresOrdinaryReset: true });
  const has = name => !!o.upgrades?.[name]?.bought;
  const unlocked = name => has(name) || !!o.upgrades?.[name]?.unlocked;
  const won = name => !!o.achievements?.[name];
  const offer = name => o.shop?.upgrades?.find(u => u.name === name && u.unlocked && !u.bought);
  const buy = (name, goal = name) => {
    const u = offer(name);
    if (!u) return null;
    if (o.cookies < u.price || !u.canBuy) return answer('needs-resources', goal, 'The native upgrade price exceeds the available bank.', null, { requiredCookies: u.price, upgrade: name });
    if (name === 'One mind') m.confirm = { name, elapsedMs: o.elapsedMs };
    return act(goal, 'Buy the unlocked native upgrade.', { type: 'buy-upgrade', id: u.id });
  };
  const S = o.seasonal;
  if (!S || !Number.isFinite(now)) return answer('blocked', 'Season observation', 'The native seasonal observation is required.');
  if (!Array.isArray(config.seasons) || config.seasons.some(s => !['valentines','christmas','halloween','easter'].includes(s))
    || !(config.maxWaitMs > 0 && Number.isFinite(config.maxWaitMs)) || !(config.petIntervalMs >= 0 && Number.isFinite(config.petIntervalMs))
    || !Number.isSafeInteger(config.reindeerTarget) || config.reindeerTarget < 0
    || !Number.isSafeInteger(config.maxSeasonUses) || config.maxSeasonUses < 1
    || !Number.isSafeInteger(config.helperMaxWidth) || config.helperMaxWidth < 200 || config.helperMaxWidth > 16384
    || !Number.isSafeInteger(config.pledgeTarget) || config.pledgeTarget < 0) return answer('blocked', 'Season configuration', 'Use supported seasons and finite nonnegative goal limits.');
  if (o.progression.onAscend || o.progression.ascensionMode !== 0 || o.progression.ascendTimer || o.progression.reincarnateTimer) return answer('blocked', 'Active normal run', 'Season collection requires an active normal run.');
  if (config.preserveChallengeAchievements && !won('Hardcore')) return answer('needs-achievement', 'Hardcore', 'Keep the no-upgrade run intact until Hardcore is won.');
  if (m.confirm) {
    const pending = m.confirm; delete m.confirm;
    if (o.controls.promptOn && o.elapsedMs === pending.elapsedMs && unlocked(pending.name) && !has(pending.name)) return act('Research confirmation', 'Confirm only the One mind purchase requested by this controller.', { type: 'prompt', option: 0 });
    return answer('blocked', 'Research confirmation', 'The expected research prompt changed or is absent.');
  }
  if (o.controls.promptOn) return answer('blocked', 'Season controls', 'Resolve the unrelated prompt first.');
  if (m.helperReleaseAt != null) {
    if (now < m.helperReleaseAt) return wait('Santa helper', 'Allow the native draw callback to process the held pointer.', m.helperReleaseAt - now);
    delete m.helperReleaseAt;
    return act('Santa helper', 'Release the native pointer after the draw callback.', { type: 'building-press', id: 1, release: true });
  }
  if (m.helperPress) {
    delete m.helperPress; m.helperReleaseAt = now + 100;
    return act('Santa helper', 'Press on the visible helper grandma.', { type: 'building-press', id: 1, release: false });
  }
  if (S.fortuneVisible && config.fortunes) return act('Fortune upgrades', 'Click the currently visible fortune.', { type: 'click-news' });

  const seasonNames = config.seasons.flatMap(s => s === 'christmas' ? ['A festive hat', ...S.groups.santa, "Santa's dominion", ...S.groups.reindeer] : S.groups[s]);
  const collection = [...(config.research ? researchNames : []), ...seasonNames,
    ...(config.dragonDrops ? dragonDrops : []), ...(config.fortunes ? S.groups.fortunes : [])];
  // Unlocks are purchased before another drop opportunity; bought eggs reduce duplicates.
  for (const name of collection) if (!has(name)) {
    const purchase = buy(name); if (purchase?.action) return purchase;
  }

  // A missing purchase or display must not suppress time-limited rewards.
  // The scheduler removes any golden cookie owned by its Fading luck hold.
  const reindeer = o.shimmers?.find(s => s.type === 'reindeer');
  const golden = o.shimmers?.find(s => s.type === 'golden');
  if (reindeer && (won('Eldeer') || !config.eldeer || o.buffs?.['Elder frenzy'] || reindeer.lifeSeconds <= 1)) return act('Christmas reindeer', 'Click the visible reindeer; preserve time for Eldeer when needed.', { type: 'click-shimmer', id: reindeer.id });
  if (golden) return act('Seasonal random rewards', 'Click a visible golden or wrath cookie without predicting its outcome.', { type: 'click-shimmer', id: golden.id });

  const targetFor = season => {
    const names = season === 'christmas' ? ['A festive hat', ...S.groups.santa, "Santa's dominion", ...S.groups.reindeer] : S.groups[season];
    return names.some(name => !has(name)) || season === 'christmas' && (o.santa.level < 14 || S.reindeerClicked < config.reindeerTarget && !(config.reindeerTarget <= 200 && won('Reindeer sleigher'))
      || config.eldeer && !won('Eldeer') || config.helperGrandma && !won("Baby it's old outside"));
  };
  const target = config.seasons.find(targetFor);
  if (target && S.season !== target) {
    if (S.uses >= config.maxSeasonUses) return retry('Season renewal',
      'Start another ordinary run before exponential season-switch prices grow further.', 'season-switch-limit');
    const trigger = { valentines: 'Lovesick biscuit', christmas: 'Festive biscuit', halloween: 'Ghostly biscuit', easter: 'Bunny biscuit' }[target];
    return buy(trigger, `${target} collection`) || answer('needs-unlock', 'Season switcher', 'The target season requires its unlocked season switch.', null, { upgrade: 'Season switcher' });
  }
  if (target === 'christmas') {
    if (has('A festive hat') && o.santa.level < 14) {
      if (o.santa.canUpgrade) return act('Santa levels', 'Pay the native Santa level cost.', { type: 'upgrade-santa' });
      return answer('needs-resources', 'Santa levels', 'Santa requires a bank strictly greater than the level price.', null, { requiredCookies: o.santa.price + Math.max(1, o.santa.price * Number.EPSILON) });
    }
    if (config.helperGrandma && !won("Baby it's old outside")) {
      const amount = o.progression.buildingAmounts.Grandma || 0;
      const display = S.grandmaDisplay;
      if (display?.muted) {
        if (!o.controls.preferences?.extraButtons) return act('Santa helper display', 'Enable the native building display controls.', { type: 'preference', name: 'extraButtons' });
        return act('Santa helper display', 'Show the Grandma display.', { type: 'building-mute', id: 1, muted: false });
      }
      if (o.controls.menu) return act('Santa helper display', 'Close the menu so the native canvas can receive pointer input.', { type: 'open-menu', menu: '' });
      const helper = S.helperGrandmas?.[0];
      if (helper) { m.helperPress = true; return act('Santa helper', 'Move to the center of a visible Santa helper grandma.', { type: 'building-hover', id: 1, x: helper.x, y: helper.y }); }
      if (m.helperResizePending) {
        const pending = m.helperResizePending;
        if (display?.width <= pending.previousWidth && now < pending.deadline) return wait('Santa helper display',
          'Allow the native draw callback to expand the visible sprite area.', 100);
        delete m.helperResizePending;
        if (display?.width <= pending.previousWidth) return retry('Santa helper retry',
          'The requested viewport has not revealed more sprite space. Request an ordinary retry run.', 'helper-display-exhausted');
      }
      if (display && display.drawn < Math.min(amount, display.capacity)) return wait('Santa helper display', 'Allow the native draw callback to show the purchased grandma.', 100);
      if (display && amount >= display.capacity) {
        const width = o.viewport?.width ?? m.helperViewportWidth ?? display.width;
        if (width < config.helperMaxWidth) {
          const wider = Math.min(config.helperMaxWidth, Math.max(width + 1, width * 2));
          m.helperViewportWidth = wider;
          m.helperResizePending = { previousWidth: display.width, deadline: now + 1000 };
          return act('Santa helper display', 'Expand the viewport once to reveal additional seeded sprite indices.',
            { type: 'resize', width: wider, height: o.viewport?.height ?? 900 });
        }
        return retry('Santa helper retry',
          'This run has no helper in the available display. Request another ordinary run before final collection.', 'helper-display-exhausted');
      }
      return answer('needs-resources', 'Santa helper', 'Add a grandma so the native Christmas display can include a helper sprite.', null, { building: 'Grandma', amount: amount + 1 });
    }
  }

  // Each quarter-hour has one fixed, seed-dependent dragon drop. Learn only from
  // drops actually observed after petting; never inspect the seed or future RNG.
  if (config.dragonDrops && dragonDrops.some(name => !has(name)) && has('Pet the dragon') && o.dragon.level >= 8) {
    const quarter = Math.floor(now / 900000);
    const phase = quarter % 4;
    const seen = dragonDrops.filter(unlocked);
    const learned = { ...(m.dragonQuarterDrops || {}) };
    const newDrops = seen.filter(name => !m.knownDragonDrops?.includes(name));
    if (m.petAttemptQuarter !== undefined && newDrops.length === 1) {
      learned[m.petAttemptQuarter % 4] = newDrops[0];
      m.petQuarterComplete = m.petAttemptQuarter;
    }
    m.dragonQuarterDrops = learned;
    m.knownDragonDrops = seen;
    // The native shuffle is a fixed permutation for this run. A mapped phase
    // with an owned drop cannot produce anything new, regardless of retries.
    if (learned[phase] && unlocked(learned[phase])) m.petQuarterComplete = quarter;
    if (m.petQuarterComplete !== quarter && now >= (m.nextPetAt || 0)) {
      // If every existing drop has a known phase, any unknown phase contains a
      // missing drop. Geometric retries then finish at this same timestamp a.s.
      // A cold-start permanent drop has no observed phase; advance time between
      // attempts so a hidden duplicate quarter cannot create an endless loop.
      const missingDropCertain = seen.every(name => Object.values(learned).includes(name));
      m.nextPetAt = now + Math.max(config.petIntervalMs, missingDropCertain ? 0 : 100);
      m.petAttemptQuarter = quarter;
      return act('Dragon drops', 'Pet the dragon during this observed quarter-hour.', { type: 'pet-dragon' });
    }
  }

  const needPoker = config.wrinklers && !won('Wrinkler poker');
  const needPop = config.wrinklers && !won('Moistburster') && o.wrinklersPopped < 200 || target === 'halloween' || target === 'easter';
  const needWrath = needPoker || needPop || target === 'christmas' && config.eldeer && !won('Eldeer');
  if (needWrath && has('Elder Covenant')) return buy('Revoke Elder Covenant', 'Restore wrinkler access') || wait('Covenant', 'Wait for the native revoke control.');
  if (needWrath && S.pledgeRemainingMs > 0) return buy('Elder Covenant', 'Restore wrinkler access') || wait('Pledge', 'Wait for the pledge to expire.', S.pledgeRemainingMs);
  if ((needPoker || needPop) && S.elderWrath > 0) {
    const wrinklers = o.controls.wrinklers.filter(w => w.phase > 0);
    let w = wrinklers.find(w => w.id === m.wrinklerTarget) || wrinklers[0];
    if (w) {
      m.wrinklerTarget = w.id;
      if (!needPoker && (target === 'halloween' || target === 'easter') && w.sucked <= 0.5) return wait('Wrinkler drops', 'Wait for a positive stored payout before requesting a seasonal drop.');
      if (now < (m.nextPokeAt || 0)) return wait('Wrinkler recovery', 'Allow native recovery before the next poke.', m.nextPokeAt - now);
      if (!w.selected) {
        m.nextPokeAt = now + 200;
        return act('Wrinkler target', 'Hover the visible wrinkler and let native hit testing select it.', { type: 'wrinkler-hover', id: w.id });
      }
      m.nextPokeAt = now + (needPoker ? 1000 : 40);
      return act(needPoker ? 'Wrinkler poker' : 'Wrinkler drops', needPoker ? 'Poke once, then allow enough recovery to keep this wrinkler alive.' : 'Poke the selected wrinkler to request its native payout.', { type: 'wrinkler-poke', id: w.id });
    }
  }

  const dropsDone = !target && (!config.wrinklers || (o.wrinklersPopped >= 200 || won('Moistburster')) && won('Wrinkler poker'));
  if (config.research && has('Elder Pact') && dropsDone) {
    if (!won('Grandmapocalypse')) return wait('Grandmapocalypse', 'Allow the native maximum-wrath achievement check before pledging.');
    if (S.pledges < config.pledgeTarget || !won('Elder calm')) {
      if (has('Elder Covenant')) return buy('Revoke Elder Covenant', 'Restore pledge access') || wait('Covenant', 'Wait for the revoke control.');
      if (S.pledgeRemainingMs > 0) return buy('Elder Covenant', 'Pledge cycle') || wait('Pledge cycle', 'Wait for the covenant control.');
      return buy('Elder Pledge', 'Pledge count') || wait('Pledge count', 'Wait for the native pledge unlock.');
    }
    if (config.pledgeTarget >= 10 && !has('Sacrificial rolling pins')) {
      const purchase = buy('Sacrificial rolling pins'); if (purchase) return purchase;
      return wait('Sacrificial rolling pins', 'Wait for the native ten-pledge check.');
    }
  }

  for (const name of collection) if (!has(name)) {
    const purchase = buy(name); if (purchase) return purchase;
  }
  if (config.research && !has('Elder Pact')) {
    if (!has('Bingo center/Research facility') && !unlocked('Bingo center/Research facility')) return answer('needs-resources', 'Research facility', 'Own six grandmas and seven Grandma synergy upgrades to unlock the research facility.', null, { building: 'Grandma', amount: 6 });
    return wait('Research', 'Wait for the current native research timer.', S.researchRemainingMs > 0 ? S.researchRemainingMs : config.maxWaitMs);
  }
  if (target || !dropsDone) return wait(target || 'Wrinkler goals', 'Wait for visible native drops, spawns, or unlock checks.');
  if (config.dragonDrops && dragonDrops.some(name => !has(name))) {
    if (!has('Pet the dragon') || o.dragon.level < 8) return answer('needs-unlock', 'Dragon pet drops', 'Pet the dragon and dragon level 8 are required.', null, { upgrade: 'Pet the dragon', dragonLevel: 8 });
    return wait('Dragon pet drops', 'Wait for another pet attempt or quarter-hour.', m.petQuarterComplete === Math.floor(now / 900000) ? 900000 - now % 900000 : Math.max(1, (m.nextPetAt || now) - now));
  }
  if (config.fortunes && S.groups.fortunes.some(name => !has(name))) {
    if (!has('Fortune cookies')) return answer('needs-unlock', 'Fortunes', 'The Fortune cookies heavenly upgrade is required.', null, { upgrade: 'Fortune cookies' });
    return wait('Fortunes', 'Wait for a naturally generated fortune in the news ticker.');
  }
  const expected = [...(config.wrinklers ? ['Wrinkler poker','Itchscratcher','Wrinklesquisher','Moistburster'] : []),
    ...(config.research ? ['Grandmapocalypse','Elder nap','Elder calm',...(config.pledgeTarget >= 5 ? ['Elder slumber'] : [])] : []),
    ...(config.fortunes ? ['O Fortuna'] : []),
    ...(config.seasons.includes('halloween') ? ['Spooky cookies'] : []),
    ...(config.seasons.includes('valentines') ? ['Lovely cookies'] : []),
    ...(config.seasons.includes('easter') ? ['The hunt is on','Egging on','Mass Easteria','Hide & seek champion'] : []),
    ...(config.seasons.includes('christmas') ? ['Coming to town','All hail Santa','Let it snow',...(config.reindeerTarget >= 200 ? ['Reindeer sleigher'] : [])] : [])];
  const pendingAchievement = expected.find(name => !won(name));
  if (pendingAchievement) return wait(pendingAchievement, 'Allow the native achievement check to record the completed condition.');
  // Golden clover does not accelerate wrath-cookie timers. Once the required
  // wrath rewards and pledge goals are done, the final count crop uses normal
  // golden cookies. The ordinary Covenant purchase carries its native CpS cost.
  if (config.suppressWrathForCookieCount && !won("Black cat's paw") && has('Elder Pact') && !has('Elder Covenant')) {
    return buy('Elder Covenant', 'Natural golden-cookie count')
      || wait('Natural golden-cookie count', 'Wait for the native Covenant control.');
  }
  return answer('complete', 'Seasonal collection', 'The configured seasonal, research, wrinkler, dragon-drop, and fortune goals are complete.');
})(observation, availableActions, {...(memory || {}), config: {...{"preserveChallengeAchievements":true}, ...((memory || {}).config || {})}}, ["Bingo center/Research facility","Specialized chocolate chips","Designer cocoa beans","Ritual rolling pins","Underworld ovens","One mind","Exotic nuts","Communal brainsweep","Arcane sugar","Elder Pact"], ["Dragon scale","Dragon claw","Dragon fang","Dragon teddy bear"]);
  }));
    const ascend = ((function(observation, availableActions, memory) {
    const decision = function ascensionDecision(o, availableActions, memory, gates, nextSevens) {
  memory ||= {};
  const config = { allowReset: false, preserveChallengeAchievements: true, growthFactor: 4,
    assignPermanentSlots: true, finalRunCookies: 1e72, continueGrowthAfterMilestones: true, earlyCountResets: false, earlyResetCookieTarget: null,
    finalGrowthAchievements: ['And a little extra', "Speed's the name of the game (no it's not it's called Cookie Clicker)", "What's not clicking"], ...memory.config };
  const m = { ...memory, config };
  const result = (status, goal, reason, action = null, extra = {}) => ({ status, goal, reason, action, memory: m, ...extra });
  const wait = (goal, reason, milliseconds = 34) => result('waiting', goal, reason, { type: 'wait', milliseconds });
  if (!(Number.isFinite(config.growthFactor) && config.growthFactor > 1) || typeof config.allowReset !== 'boolean'
    || !(Number.isFinite(config.finalRunCookies) && config.finalRunCookies >= 1e57)
    || !(config.earlyResetCookieTarget === null || Number.isFinite(config.earlyResetCookieTarget) && config.earlyResetCookieTarget >= 1e12)
    || !Array.isArray(config.finalGrowthAchievements) || config.finalGrowthAchievements.some(name => typeof name !== 'string')) {
    return result('blocked', 'Ascension configuration', 'Use a finite growth factor above one and an explicit reset permission.');
  }
  const A = o.ascension;
  const P = o.progression;
  if (!A || !P || A.heavenlyUpgrades?.length !== 129) return result('blocked', 'Ascension observation', 'The complete pinned heavenly inventory is required.');
  const heavenly = A.heavenlyUpgrades;
  const byId = new Map(heavenly.map(u => [u.id, u]));
  const byName = new Map(heavenly.map(u => [u.name, u]));
  const won = name => !!o.achievements?.[name];
  const missing = heavenly.filter(u => !u.bought);
  const gate = gates.find(g => !byName.get(g.name)?.bought);
  const countSevens = value => (String(value).match(/7/g) || []).length;
  const parentsMet = u => u.parents.every(id => byId.get(id)?.bought);
  function closure(upgrade) {
    const done = new Set(); const visiting = new Set(); const list = [];
    function visit(u) {
      if (!u || visiting.has(u.id)) throw new Error('Invalid heavenly dependency graph');
      if (u.bought || done.has(u.id)) return;
      visiting.add(u.id);
      for (const id of u.parents) visit(byId.get(id));
      visiting.delete(u.id); done.add(u.id); list.push(u);
    }
    visit(upgrade); return list;
  }
  const slotNames = ['I', 'II', 'III', 'IV', 'V'].map(n => `Permanent upgrade slot ${n}`);
  const candidate = () => [...(A.permanentCandidates || [])].sort((a, b) =>
    Number(/kitten/i.test(b.name)) - Number(/kitten/i.test(a.name)) || b.price - a.price || a.id - b.id)[0];
  if (o.controls?.promptOn) {
    if (m.pendingSlot !== undefined && P.onAscend) {
      const slot = m.pendingSlot; delete m.pendingSlot;
      const chosen = config.assignPermanentSlots ? candidate() : null;
      if (chosen) return result('acting', 'Permanent upgrade', 'Assign a legal owned upgrade in this controller’s slot prompt.', { type: 'permanent-slot', slot, id: chosen.id });
      return result('acting', 'Permanent upgrade', 'Close this controller’s empty assignment prompt.', { type: 'close-prompt' });
    }
    return result('blocked', 'Ascension prompt', 'Resolve the unrelated prompt before changing runs.');
  }
  delete m.pendingSlot;
  if (P.ascendTimer > 0) {
    if (!m.escapeSent) {
      m.escapeSent = true;
      return result('acting', 'Ascension transition', 'Use the native Escape release to finish the ascension animation.', { type: 'key', code: 27, down: false });
    }
    return wait('Ascension transition', 'Allow the next native frame to enter the ascension screen.');
  }
  delete m.escapeSent;
  if (P.reincarnateTimer > 0) return wait('Reincarnation transition', 'Wait for the native reincarnation animation.', 100);
  if (P.onAscend) {
    let eligible = heavenly.filter(u => !u.bought && u.visible && parentsMet(u) && u.price <= o.heavenlyChips);
    // Reserve an affordable visible digit-gated ancestor closure before buying
    // unrelated upgrades. Checking only individual affordability loses the gate.
    if (gate && byName.get(gate.name).visible) {
      const needed = closure(byName.get(gate.name));
      if (needed.reduce((sum, u) => sum + u.price, 0) <= o.heavenlyChips) {
        const ids = new Set(needed.map(u => u.id)); eligible = eligible.filter(u => ids.has(u.id));
      }
    }
    eligible.sort((a, b) => a.price - b.price || a.id - b.id);
    if (eligible.length) {
      const upgrade = eligible[0];
      const slot = slotNames.indexOf(upgrade.name);
      if (slot >= 0) m.pendingSlot = slot;
      return result('acting', 'Heavenly upgrades', `Buy ${upgrade.name} after its parents.`, { type: 'buy-upgrade', id: upgrade.id });
    }
    if (config.assignPermanentSlots) {
      const slot = slotNames.findIndex((name, i) => byName.get(name)?.bought && A.permanentSlots?.[i] === -1);
      const chosen = candidate();
      if (slot >= 0 && chosen) return result('acting', 'Permanent upgrade', 'Fill an unlocked empty slot with a legal owned upgrade.', { type: 'permanent-slot', slot, id: chosen.id });
    }
    m.completedCycles = (m.completedCycles || 0) + 1;
    return result('acting', 'Normal reincarnation', 'Return to a normal run after buying the available heavenly upgrades.', { type: 'reincarnate', mode: 0 });
  }
  if (P.ascensionMode !== 0) return result('blocked', 'Normal run', 'This schedule requires normal mode.');
  if (config.preserveChallengeAchievements && (!won('Hardcore') || !won('Neverclick'))) {
    return result('needs-achievement', 'First-run achievements', 'Win Hardcore and Neverclick before the first reset.');
  }
  // The constructive early-count phase precedes digit gates and growth resets.
  // It uses actual earned cookies and positive native prestige, not a counter
  // assigned by the scheduler. Later zero-profit resets cannot satisfy it.
  if (config.earlyCountResets && config.earlyResetCookieTarget !== null && o.ascensions < 100) {
    if (!config.allowReset) return result('deferred', 'Early profitable ascensions',
      'The scheduler has not permitted the early-count reset phase.');
    if (o.cookiesEarned < config.earlyResetCookieTarget) return result('needs-resources', 'Early profitable ascensions',
      'Earn the fixed current-run target before this ordinary ascension.', null,
      { requiredCookiesEarned: config.earlyResetCookieTarget, completedProfitableResets: o.ascensions });
    if (!(A.gainedIfAscend > 0 && Number.isFinite(A.gainedIfAscend))) return result('needs-prestige', 'Early profitable ascensions',
      'Continue native growth until prestige gain is positive; a zero-profit reset would not advance the required count.', null,
      {requiredCookiesEarned: config.earlyResetCookieTarget, targetPrestige: o.prestige + Math.max(1, o.prestige * Number.EPSILON)});
    return result('acting', 'Early profitable ascensions', 'Ascend after the fixed earned-cookie target and positive native gain.', {type:'ascend'});
  }
  const allResetGoals = ['Rebirth', 'Resurrection', 'Reincarnation', 'All the stars in heaven', 'No more room in hell', 'Debt evasion'];
  const resetMilestonesDone = !missing.length && allResetGoals.every(won) && o.ascensions >= 100;
  // The default baked-cookie target is a persistent native achievement. A
  // later seasonal retry must not force the same growth milestone again.
  // Larger custom targets have no such native history certificate here.
  const runGoalReached = o.cookiesEarned >= config.finalRunCookies
    || config.finalRunCookies <= 1e72 && won('And a little extra');
  if (resetMilestonesDone && (!config.continueGrowthAfterMilestones
    || runGoalReached && config.finalGrowthAchievements.every(won))) {
    return result('complete', 'Ascension goals', 'Remain in this normal run to finish its ordinary upgrades and other current-state goals.');
  }
  const future = A.prestigeIfAscend;
  const gain = A.gainedIfAscend;
  if (!Number.isFinite(future) || !Number.isFinite(gain) || gain < 0) return result('blocked', 'Prestige arithmetic', 'The observed native prestige gain is invalid.');
  let gatePlan = null;
  if (gate) {
    const needed = closure(byName.get(gate.name));
    const cost = needed.reduce((sum, u) => sum + u.price, 0);
    const required = Math.max(future, o.prestige + Math.max(1, Math.ceil(cost - o.heavenlyChips)));
    const target = nextSevens(required, gate.sevens);
    gatePlan = { upgrade: gate.name, sevens: gate.sevens, requiredChips: cost, targetPrestige: target,
      targetLifetimeCookies: target === null ? null : target ** 3 * 1e12 };
    if (countSevens(future) >= gate.sevens && o.heavenlyChips + gain >= cost) gatePlan.ready = true;
    if (!gatePlan.ready && target === null) return result('blocked-range', gate.name,
      'No finite cookie target was found within this planner’s numeric range. This does not prove the native upgrade unreachable.', null, { gatePlan });
  }
  const newlyAffordable = missing.some(u => parentsMet(u) && u.price > o.heavenlyChips && u.price <= o.heavenlyChips + gain
    && (!gates.some(g => g.name === u.name) || countSevens(future) >= gates.find(g => g.name === u.name).sevens));
  let goal = null;
  if (gatePlan?.ready) goal = gatePlan.upgrade;
  else if (!won('No more room in hell') && o.cookiesEarned >= 1e57) goal = 'No more room in hell';
  else if (!won('All the stars in heaven') && heavenly.filter(u => u.bought).length >= 100) goal = 'All the stars in heaven';
  else if ((missing.length || (resetMilestonesDone && config.continueGrowthAfterMilestones))
    && gain > 0 && (newlyAffordable || gain >= Math.max(1, Math.ceil(o.prestige * (config.growthFactor - 1))))) goal = 'Heavenly growth';
  else if ((!missing.length || config.earlyCountResets) && o.ascensions < 100 && gain > 0) goal = 'Reincarnation';
  else if (!won('Debt evasion') && o.market?.loans?.some(l => l.unlocked)) goal = 'Debt evasion';
  if (goal) {
    if (!config.allowReset) return result('deferred', goal, 'The scheduler must release the current Garden and market work before a reset.', null, { gatePlan });
    if (!won('Debt evasion')) {
      const activeLoan = o.market?.loans?.some(l => l.activeFrames > 0);
      const loan = o.market?.loans?.find(l => l.unlocked && l.activeFrames === 0 && l.interestFrames === 0);
      if (!activeLoan && loan && o.market?.open === false) return result('acting', 'Debt evasion', 'Open the market panel before starting the loan.', { type: 'minigame-open', id: o.market.buildingId ?? 5 }, { gatePlan });
      if (!activeLoan && loan?.visible === false) return wait('Debt evasion', 'Wait for the native loan control to become visible before this ascension.', 1000);
      if (!activeLoan && loan) return result('acting', 'Debt evasion', 'Take an available loan immediately before this planned ascension.', { type: 'market-loan', id: loan.id }, { gatePlan });
      if (goal === 'Debt evasion' && !activeLoan) return wait('Debt evasion', 'Wait for an available loan; an interest period does not qualify.', 1000);
    }
    return result('acting', goal, 'Ascend after the scheduler has released the current run.', { type: 'ascend' }, { gatePlan });
  }
  if (gatePlan) return result('needs-prestige', gatePlan.upgrade, 'Grow toward the next observable prestige value with the required sevens. Stop and recheck the native value before ascending.', null, { gatePlan });
  if (missing.length) {
    const cheapest = missing.filter(parentsMet).sort((a,b) => a.price - b.price || a.id - b.id)[0];
    return result('needs-prestige', 'Heavenly upgrades', 'Earn more heavenly chips for the remaining upgrades.', null,
      { requiredChips: cheapest?.price ?? null, targetPrestige: o.prestige + Math.max(1, (cheapest?.price || 1) - o.heavenlyChips) });
  }
  if (!won('No more room in hell')) return result('needs-resources', 'No more room in hell', 'Bake at least 1e57 cookies within one run before its reset.', null, { requiredCookiesEarned: 1e57 });
  if (o.ascensions < 100) return result('needs-prestige', 'Reincarnation', 'Each counted reset needs a positive native prestige gain.', null,
    { targetPrestige: o.prestige + Math.max(1, o.prestige * Number.EPSILON) });
  if (!won('Debt evasion')) return result('needs-resources', 'Debt evasion', 'Unlock a Stock Market loan before the final required reset.', null, { officeLevel: 2 });
  if (resetMilestonesDone) return result('needs-resources', 'Final run growth', 'Grow this run, with further resets only after scheduler permission.', null,
    { requiredCookiesEarned: config.finalRunCookies, missingGrowthAchievements: config.finalGrowthAchievements.filter(name => !won(name)), targetPrestige: o.prestige * config.growthFactor });
  return result('blocked', 'Ascension achievements', 'A required native reset achievement is still absent.');
};
    const nextSevens = function nextSevenPrestige(start, count) {
  if (!Number.isFinite(start) || !Number.isInteger(start) || start < 0 || !Number.isInteger(count) || count < 1 || count > 4) return null;
  const text = String(start);
  for (let length = text.length; Number.isSafeInteger(start) && length <= 16; length++) {
    const floor = text.padStart(length, '0');
    const dead = new Set();
    function fill(position, found, tight) {
      if (position === length) return found >= count ? '' : null;
      if (found + length - position < count) return null;
      const key = `${position},${Math.min(found, count)},${tight}`;
      if (dead.has(key)) return null;
      const minimum = Math.max(position === 0 && length > 1 ? 1 : 0, tight ? Number(floor[position]) : 0);
      for (let digit = minimum; digit <= 9; digit++) {
        const tail = fill(position + 1, found + Number(digit === 7), tight && digit === Number(floor[position]));
        if (tail !== null) return String(digit) + tail;
      }
      dead.add(key); return null;
    }
    const digits = fill(0, 0, true);
    if (digits !== null) {
      const value = Number(digits);
      if (Number.isSafeInteger(value)) return value;
      break;
    }
  }
  // Large native prestige levels have a finite binary64 spacing. Request a
  // wide leading-7 interval instead of an unrepresentable next integer. The
  // buffer survives the cube/cube-root rounding used by the pinned engine.
  // This supplies a concrete candidate, not the nearest large-number target.
  // At these magnitudes all three gate costs are small relative to the target;
  // keep four leading sevens so one visit can collect all of them.
  const base = 7777;
  const exponent = Math.floor(Math.log10(Math.max(1, start))) - 3;
  for (let shift = 0; shift < 5; shift++) {
    const nominal = base * 10 ** (exponent + shift);
    const cookies = nominal ** 3 * 1e12 * (1 + 1e-10);
    if (!Number.isFinite(cookies)) continue;
    const nativePrestige = Math.floor(Math.pow(cookies / 1e12, 1 / 3));
    if (nativePrestige >= start && (String(nativePrestige).match(/7/g) || []).length >= count) return nativePrestige;
  }
  return null;
};
    return decision(observation, availableActions, {...(memory || {}), config: {...{"allowReset":true,"preserveChallengeAchievements":true,"earlyCountResets":true,"earlyResetCookieTarget":1.2379400392853803e+27}, ...((memory || {}).config || {})}},
      [{"name":"Lucky digit","sevens":1},{"name":"Lucky number","sevens":2},{"name":"Lucky payout","sevens":4}], nextSevens);
  }));
    const produce = ((function(observation,availableActions,memory){return (function productionDecision(o, actions, memory) {
  const config={finalCollection:false,preserveChallengeAchievements:true,buyOrdinaryUpgrades:true,clickRate:20,maxWaitMs:1000,...(memory?.config||{})};
  const m={...(memory||{}),config};
  const result=(status,goal,reason,action=null,extra={})=>({status,goal,reason,action,memory:m,...extra});
  const won=name=>!!o.achievements?.[name];
  if(!config.finalCollection)return result('deferred','Final-run collection','The scheduler must finish its planned resets before requesting final current ownership.');
  if(!Number.isFinite(config.clickRate)||config.clickRate<0||config.clickRate>50||!Number.isFinite(config.maxWaitMs)||config.maxWaitMs<=0)return result('blocked','Production configuration','Use a click rate from zero to fifty and a positive finite wait limit.');
  const p=o.progression;
  if(p.onAscend||p.ascendTimer||p.reincarnateTimer||p.ascensionMode!==0)return result('blocked','Final normal run','Production collection requires an active normal run.');
  if(o.controls.promptOn)return result('blocked','Production controls','Resolve the unrelated prompt before purchases.');
  if(config.preserveChallengeAchievements&&(!won('Hardcore')||!won('Neverclick')))return result('needs-achievement','First-run challenges','Preserve the no-upgrade and limited-click conditions until both achievements are won.');
  const buildings=o.shop?.buildings;
  const targets=o.production;
  if(buildings?.length!==20||!targets?.bankAchievements?.length||!targets.cpsAchievements?.length||targets.handmadeAchievements?.length!==15)return result('blocked','Production catalogue','The pinned native production thresholds are required.');
  const deficient=buildings.filter(b=>b.amount<b.goalAmount).sort((a,b)=>a.buy1price-b.buy1price||a.id-b.id);
  for(const b of deficient) {
    if(b.locked)continue;
    const amount=b.goalPurchase.amount;
    if(amount>0&&o.cookies>=b.goalPurchase.price)return result('acting','Final building counts','Buy the native batch needed for this current holding.',{type:'buy-building',id:b.id,amount},{building:b.name,targetAmount:b.goalAmount});
    if(o.cookies>=b.buy1price)return result('acting','Final building counts','Add one affordable building toward its current holding target.',{type:'buy-building',id:b.id,amount:1},{building:b.name,targetAmount:b.goalAmount});
  }
  if(config.buyOrdinaryUpgrades) {
    // One mind owns a confirmation workflow in the research controller.
    const u=o.shop.upgrades.filter(u=>!['toggle','prestige','debug','unused','dungeon','shadow'].includes(u.pool)&&u.name!=='One mind'&&u.canBuy&&u.price<=o.cookies)
      .sort((a,b)=>a.price-b.price||a.id-b.id)[0];
    if(u)return result('acting','Current ordinary upgrades','Buy an unlocked ordinary upgrade at its native displayed price.',{type:'buy-upgrade',id:u.id});
  }
  const handmadeMissing=targets.handmadeAchievements.filter(a=>!won(a.name));
  if(handmadeMissing.length&&config.clickRate>0&&o.elapsedMs>=(m.nextClickAt??100)) {
    m.nextClickAt=o.elapsedMs+1000/config.clickRate;
    return result('acting','Handmade production','Click without predicting a random outcome.',{type:'click'});
  }
  if(deficient.length) {
    const b=deficient[0];
    return result('needs-resources','Final building counts','Grow the bank before the next count purchase.',null,{building:b.name,buildingId:b.id,targetAmount:b.goalAmount,requiredCookies:b.buy1price,fullBatchCookies:b.goalPurchase.price});
  }
  const missingProduction=buildings.flatMap(b=>b.productionAchievements.filter(a=>!won(a.name)).map(a=>({building:b.name,buildingId:b.id,achievement:a.name,target:a.threshold,produced:b.totalCookies,
    secondsAtCurrentRate:b.productionCps>0?Math.max(0,(a.threshold-b.totalCookies)/b.productionCps):null})));
  const missingBank=targets.bankAchievements.filter(a=>!won(a.name));
  const missingCps=targets.cpsAchievements.filter(a=>!won(a.name));
  const countChecks=buildings.flatMap(b=>b.countAchievements).filter(a=>!won(a.name));
  const pending=missingProduction.length||missingBank.length||missingCps.length||handmadeMissing.length||countChecks.length||!won('Septcentennial');
  if(!pending)return result('complete','Final production and counts','All native production families and count achievements are won, and current building holdings meet their targets.');
  const nextClick=config.clickRate>0&&handmadeMissing.length?Math.max(1,(m.nextClickAt??100)-o.elapsedMs):config.maxWaitMs;
  return result('needs-production','Production milestones','Continue growth and native production; the rate estimates assume unchanged rates and are not completion-time bounds.',
    {type:'wait',milliseconds:Math.min(config.maxWaitMs,nextClick)},
    {requiredRawCps:missingCps.at(-1)?.threshold??null,requiredCookiesEarned:missingBank.at(-1)?.threshold??null,requiredHandmadeCookies:handmadeMissing.at(-1)?.threshold??null,
      missingProduction, pendingCountChecks:countChecks.map(a=>a.name)});
})(observation,availableActions,{...(memory||{}),config:{...{"clickRate":50,"preserveChallengeAchievements":true},...((memory||{}).config||{})}});}));
    const combine = ((function(observation,availableActions,memory){return (function comboDecision(o, availableActions, memory, identities) {
  const config = { clickRate: 20, preserveChallengeAchievements: true, configurePantheon: true,
    configureAuras: true, castHandOfFate: true, godzamok: true, reserveCookies: 0,
    cycleIntervalMs: 100, minimumBuffSeconds: 1, profitMargin: 2, maximumCycleBankShare: 0.05,
    auraPaybackSeconds: 1800, deferredShimmerIds: [], ...memory?.config };
  let m = { ...memory, config };
  const result = (status, goal, reason, action = null, extra = {}) => ({ status, goal, reason, action,
    memory: m, exclusive: false, reserveCookies: 0, reserveMagic: 0, optimalityCertified: false, ...extra });
  const valid = Number.isFinite(config.clickRate) && config.clickRate >= 0 && config.clickRate <= 50
    && Number.isFinite(config.cycleIntervalMs) && config.cycleIntervalMs >= 20
    && Number.isFinite(config.minimumBuffSeconds) && config.minimumBuffSeconds > 0
    && Number.isFinite(config.profitMargin) && config.profitMargin >= 1
    && Number.isFinite(config.maximumCycleBankShare) && config.maximumCycleBankShare > 0 && config.maximumCycleBankShare <= 1
    && Number.isFinite(config.reserveCookies) && config.reserveCookies >= 0
    && Number.isFinite(config.auraPaybackSeconds) && config.auraPaybackSeconds > 0
    && Array.isArray(config.deferredShimmerIds);
  if (!valid) return result('blocked', 'Combo configuration', 'Use finite rates, reserves, and positive cost limits.');
  const p = o.progression;
  if (!p || !o.controls || !o.shop?.buildings) return result('blocked', 'Combo observation', 'The native public control and building observations are required.');
  if (![o.cookies, o.cookiesPs, o.elapsedMs].every(Number.isFinite) || o.cookies < 0 || o.elapsedMs < 0) {
    return result('blocked', 'Combo arithmetic', 'Finite bank, production, and clock values are required.');
  }
  if (m.run !== undefined && m.run !== o.ascensions) m = { config, run: o.ascensions };
  m.run = o.ascensions;
  if (p.onAscend || p.ascendTimer || p.reincarnateTimer || p.ascensionMode !== 0) {
    return result('deferred', 'Normal run', 'Wait for an active normal run before combo controls.');
  }
  const bank = Math.max(0, o.cookies - config.reserveCookies);
  const buildings = o.shop.buildings;
  const byId = id => buildings.find(b => b.id === id);
  const priceSignature = () => JSON.stringify([o.dragon?.aura, o.dragon?.aura2,
    o.controls.pantheon?.slots, Object.entries(o.upgrades || {}).filter(([, u]) => u.bought).map(([name]) => name),
    ['Everything must go', 'Crafty pixies', 'Nasty goblins'].map(name => !!o.buffs?.[name]),
    o.garden?.plot, o.garden?.soil, o.garden?.freeze]);
  // A sale is a two-action transaction. The scheduler must restore it before other controls.
  if (m.rebuy) {
    const pending = m.rebuy;
    const b = byId(pending.id);
    if (!b) return result('blocked', 'Restore sold buildings', 'The recorded building is absent.', null, { exclusive: true });
    const missing = Math.max(0, pending.targetAmount - b.amount);
    if (!missing) delete m.rebuy;
    else {
      if (!Number.isInteger(missing) || missing > 1000) return result('blocked', 'Restore sold buildings', 'The recorded purchase exceeds the native batch limit.', null, { exclusive: true });
      const unchanged = missing === pending.amount && o.elapsedMs === pending.time && priceSignature() === pending.priceSignature;
      // An interrupted pair is restored one currently quoted copy at a time.
      // Do not extrapolate a bulk buyback through changed discounts or rounding.
      const purchaseAmount = unchanged ? missing : 1;
      const required = unchanged ? pending.rebuy : b.buy1price;
      if (!Number.isFinite(required) || bank < required) return result('needs-resources', 'Restore sold buildings',
        'Keep this transaction reserved until its current native purchase is funded.', null,
        { exclusive: true, reserveCookies: required, requiredCookies: required });
      return result('acting', 'Restore sold buildings', 'Buy back the recorded copies before another action changes prices.',
        { type: 'buy-building', id: b.id, amount: purchaseAmount }, { exclusive: true, reserveCookies: required });
    }
  }
  if (m.confirmAura) {
    const pending = m.confirmAura;
    if (o.controls.promptOn) {
      if (o.elapsedMs !== pending.time || o.dragon?.level !== pending.level ||
          (pending.buildingId !== null && byId(pending.buildingId)?.amount !== pending.beforeAmount)) {
        return result('blocked', 'Owned dragon prompt', 'The aura prompt state changed; do not confirm it automatically.', null, { exclusive: true });
      }
      delete m.confirmAura;
      if (pending.buildingId !== null) m.auraRestore = { id: pending.buildingId, targetAmount: pending.beforeAmount };
      return result('acting', 'Dragon aura', 'Confirm only the aura prompt requested by this controller.',
        { type: 'prompt', option: 0 }, { exclusive: true, reserveCookies: pending.reserve });
    }
    delete m.confirmAura;
  }
  if (m.auraRestore) {
    const b = byId(m.auraRestore.id);
    if (!b || b.amount >= m.auraRestore.targetAmount) delete m.auraRestore;
    else {
      if (bank < b.buy1price) return result('needs-resources', 'Restore aura sacrifice', 'Fund the current native replacement price.', null,
        { exclusive: true, reserveCookies: b.buy1price, requiredCookies: b.buy1price });
      return result('acting', 'Restore aura sacrifice', 'Restore the highest building sacrificed by the aura prompt.',
        { type: 'buy-building', id: b.id, amount: 1 }, { exclusive: true, reserveCookies: b.buy1price });
    }
  }
  if (o.controls.promptOn) return result('deferred', 'Unowned prompt', 'This controller does not confirm another controller’s prompt.');
  if (config.preserveChallengeAchievements && (!o.achievements?.Hardcore || !o.achievements?.Neverclick)) {
    return result('needs-achievement', 'First-run challenges', 'Preserve the challenge conditions before setting up active combos.');
  }
  const P = o.controls.pantheon;
  if (config.configurePantheon && config.clickRate > 0 && p.minigames?.Temple && P?.swaps > 0) {
    const desired = ['ruin', 'labor', 'mother'];
    const slot = desired.findIndex((key, i) => P.slots[i] !== identities.gods[key]);
    if (slot !== -1) return result('acting', 'Active Pantheon', 'Use Godzamok, Muridal, and Mokalsium for this active-click schedule.',
      { type: 'pantheon-slot', god: desired[slot], slot });
  }
  // Fill empty slots only. Existing sugar, Garden, or other deliberately chosen auras stay in place.
  if (config.configureAuras && o.upgrades?.['A crumbly egg']?.bought && o.dragon?.auras) {
    const D = o.dragon;
    const ownedKitten = Object.entries(o.upgrades || {}).some(([name, u]) => /^Kitten /i.test(name) && u.bought);
    const targets = ['Radiant Appetite', ...(ownedKitten ? ['Breath of Milk'] : [])];
    const current = [D.aura, D.aura2];
    const slot = current.findIndex((id, i) => id === 0 && (i === 0 || D.level === 27));
    const aura = slot === -1 ? null : targets.map(name => D.auras.find(a => a.name === name && a.unlocked && !current.includes(a.id))).find(Boolean);
    if (aura) {
      const highest = [...buildings].reverse().find(b => b.amount > 0);
      const reserve = highest ? highest.buy1price * 1.05 : 0;
      const estimatedGain = aura.name === 'Radiant Appetite' ? o.cookiesPs : o.cookiesPs * 0.01;
      if (Number.isFinite(reserve) && bank >= reserve && estimatedGain * config.auraPaybackSeconds >= reserve) {
        m.confirmAura = { id: aura.id, slot, time: o.elapsedMs, level: D.level,
          buildingId: highest?.id ?? null, beforeAmount: highest?.amount ?? 0, reserve };
        return result('acting', 'Dragon aura', 'Fill an empty aura slot after funding its building replacement.',
          { type: 'dragon-aura', id: aura.id, slot }, { exclusive: true, reserveCookies: reserve });
      }
    }
  }
  const buffs = Object.values(o.buffs || {});
  const fps = Number.isFinite(o.fps) && o.fps > 0 ? o.fps : 30;
  const positive = buffs.filter(b => b.time / fps >= config.minimumBuffSeconds && (b.multCpS > 1 || b.multClick > 1));
  const shimmer = o.shimmers?.find(s => s.type === 'golden' && !config.deferredShimmerIds.includes(s.id));
  if (shimmer && (m.awaitingSpell || positive.length)) {
    delete m.awaitingSpell;
    return result('acting', 'Observed golden cookie', 'Click the visible cookie without predicting its effect.', { type: 'click-shimmer', id: shimmer.id });
  }
  if (m.awaitingSpell && !o.shimmers?.some(s => s.type === 'golden')) delete m.awaitingSpell;
  const M = o.controls.grimoire;
  const fate = M?.spells?.['hand of fate'];
  const reserveMagic = config.castHandOfFate && fate ? fate.cost : 0;
  if (config.castHandOfFate && positive.length && p.minigames?.['Wizard tower'] && fate && M.magic >= fate.cost
      && !o.shimmers?.some(s => s.type === 'golden') && o.elapsedMs >= (m.nextCastAt || 0)) {
    m.awaitingSpell = true; m.nextCastAt = o.elapsedMs + 1000;
    return result('acting', 'Observed-buff spell', 'Cast Force the Hand of Fate during an observed positive buff, with no golden cookie already present.',
      { type: 'cast-spell', spell: 'hand of fate' }, { reserveMagic });
  }
  const ruinSlot = P?.slots?.indexOf(identities.gods.ruin) ?? -1;
  const bonus = [0.01, 0.005, 0.0025][ruinSlot] || 0;
  const devastation = o.buffs?.Devastation;
  const seconds = devastation ? devastation.time / fps : 10;
  const basePerClick = o.cookiesPerClick / (devastation?.multClick || 1);
  if (config.godzamok && config.clickRate > 0 && bonus && seconds >= config.minimumBuffSeconds
      && Number.isFinite(basePerClick) && basePerClick > 0 && o.elapsedMs >= (m.nextCycleAt || 0)) {
    const protectedNames = ['Cursor', 'Grandma', 'Farm', 'Bank', 'Temple', 'Wizard tower', 'You'];
    const choices = buildings.filter(b => !protectedNames.includes(b.name) && !b.locked).map(b => {
      const q = b.godzamokCycle;
      if (!q || !Number.isInteger(q.amount) || q.amount < 1 || q.amount > 100 || b.amount - q.amount < 1
        || ![q.rebuy, q.refund, q.net].every(Number.isFinite) || q.rebuy < 0 || q.net < 0) return null;
      // Do not assume another observed positive buff lasts for the whole Devastation window.
      const stableSeconds = Math.min(seconds, ...buffs.filter(buff => buff.time > 0).map(buff => buff.time / fps));
      if (stableSeconds < config.minimumBuffSeconds) return null;
      const additional = bonus * q.amount * config.clickRate * basePerClick * stableSeconds;
      if (q.rebuy > bank * config.maximumCycleBankShare || additional <= config.profitMargin * q.net) return null;
      return { b, q, additional, ratio: additional / Math.max(q.net, 1) };
    }).filter(Boolean).sort((a, b) => b.ratio - a.ratio || a.b.id - b.b.id);
    if (choices.length) {
      const { b, q, additional } = choices[0];
      m.rebuy = { id: b.id, amount: q.amount, targetAmount: b.amount, rebuy: q.rebuy,
        time: o.elapsedMs, priceSignature: priceSignature() };
      m.nextCycleAt = o.elapsedMs + config.cycleIntervalMs;
      return result('acting', 'Funded Godzamok cycle', 'Sell only a funded batch whose estimated extra clicks exceed its round-trip cost margin.',
        { type: 'sell-building', id: b.id, amount: q.amount },
        { exclusive: true, reserveCookies: q.rebuy, reserveMagic, estimatedAdditionalCookies: additional, roundTripCost: q.net });
    }
  }
  if (positive.length && config.clickRate > 0 && o.elapsedMs >= (m.nextClickAt ?? 100)) {
    m.nextClickAt = o.elapsedMs + 1000 / config.clickRate;
    return result('acting', 'Observed-buff clicks', 'Use the configured native-safe click cadence during the observed buff.', { type: 'click' }, { reserveMagic });
  }
  return result('idle', 'Combo growth', 'Wait for an observed opportunity while other controllers continue.', null, { reserveMagic });
})(observation,availableActions,{...(memory||{}),config:{...{"clickRate":50,"preserveChallengeAchievements":true},...((memory||{}).config||{})}},{"gods":{"asceticism":0,"decadence":1,"ruin":2,"ages":3,"seasons":4,"creation":5,"labor":6,"industry":7,"mother":8,"scorn":9,"order":10},"auras":{"No aura":0,"Breath of Milk":1,"Dragon Cursor":2,"Elder Battalion":3,"Reaper of Fields":4,"Earth Shatterer":5,"Master of the Armory":6,"Fierce Hoarder":7,"Dragon God":8,"Arcane Aura":9,"Dragonflight":10,"Ancestral Metamorphosis":11,"Unholy Dominion":12,"Epoch Manipulator":13,"Mind Over Matter":14,"Radiant Appetite":15,"Dragon's Fortune":16,"Dragon's Curve":17,"Reality Bending":18,"Dragon Orbs":19,"Supreme Intellect":20,"Dragon Guts":21}});}));
    const fund = ((function(o,actions,memory){return (function fundingDecision(o, memory, options) {
  const config={cycles:16384,batchCycles:128,clickRate:50,...options};
  config.clicks??=Math.min(400,Math.floor(config.clickRate*8));
  let m={...(memory || {})};
  const result=(status,reason,action=null)=>({status,reason,action,memory:m,exclusive:!!m.phase && !['complete','interrupted'].includes(m.phase),optimalityCertified:false});
  if(!Number.isSafeInteger(config.cycles)||config.cycles<1||config.cycles>65536
    || !Number.isSafeInteger(config.batchCycles)||config.batchCycles<1||config.batchCycles>249
    || !Number.isFinite(config.clickRate)||config.clickRate<=0||config.clickRate>50
    || !Number.isSafeInteger(config.clicks)||config.clicks<1||config.clicks>400||config.clicks/config.clickRate>8)
    return result('blocked','Use finite bounded cycle and native click batches.');
  const interrupted=reason=>{m.phase='interrupted';m.interruptionReason=reason;return result('interrupted',reason);};
  if(m.phase==='interrupted')return result('interrupted',m.interruptionReason);
  const p=o.progression,c=o.controls,b=o.shop?.buildings?.find(x=>x.name==='Cursor');
  const unavailable=reason=>m.phase?interrupted(reason):result('deferred',reason);
  if(!p||!c||!b||p.onAscend||p.ascendTimer||p.reincarnateTimer||p.ascensionMode!==0||c.promptOn||c.menu)
    return unavailable('An active normal run with visible store controls is required.');
  if(!o.achievements.Hardcore||!o.achievements.Neverclick)return unavailable('Finish the first-run challenges first.');
  if(!p.minigames.Temple||!o.shop.buildings.some(x=>x.name==='Temple'&&x.amount>0)||c.pantheon?.slots?.[0]!==2)return unavailable('The native diamond Godzamok slot must be active.');
  if(!o.upgrades?.['Plastic mouse']?.bought)return unavailable('Buy the ordinary CpS-based click upgrade before funding bursts.');
  if(o.buffs?.['Cursed finger'])return unavailable('Let Cursed finger finish before starting a funding burst.');
  if(o.buffs?.['Nasty goblins'])return unavailable('Wait for the temporary building-price penalty to end.');
  if(!Number.isFinite(o.cookies)||o.cookies<0||!Number.isFinite(o.cookiesPerClick)||o.cookiesPerClick<=0)
    return unavailable('Finite positive native income is required.');
  if(m.run!==undefined&&m.run!==o.ascensions)return interrupted('A reset interrupted the owned burst.');
  const bulk=id=>({type:'store-bulk',id}),product={type:'click-product',id:0};
  const sequence=actions=>({type:'sequence',actions});
  if(!m.phase){
    const otherCps=o.shop.buildings.filter(x=>x.id!==0).reduce((sum,x)=>sum+(x.productionCps||0),0);
    const stableBuffs=Object.values(o.buffs||{}).every(x=>!(x.multCpS>1)||x.time/o.fps>9);
    const amount=o.cookies>=2**50 && otherCps*.01*config.clicks>=2**34 && stableBuffs ? 100 : 1;
    const lossPerCycle=amount===100?2**32:16;
    if(o.cookies<lossPerCycle*config.cycles+100000)return result('deferred','Reserve every possible native purchase debit before the burst.');
    m={run:o.ascensions,phase:'setup',originalCursors:b.amount,completed:0,amount,lossPerCycle,bulkId:amount===100?4:2};
    if(b.amount!==m.amount){
      const actions=b.amount>0?[bulk(1),bulk(5),product]:[];
      actions.push(bulk(0),bulk(m.bulkId),product);
      return result('acting','Use native controls to retain the selected Cursor batch and all sale proceeds.',sequence(actions));
    }
  }
  if(b.amount!==m.amount)return result('blocked','Native setup did not leave the selected Cursor count.');
  if(b.price>(m.amount===100?20000000:18)||b.rebuyOnePrice>(m.amount===100?20000000:15)||!Number.isFinite(b.price)||!Number.isFinite(b.rebuyOnePrice))
    return result('blocked','The quoted Cursor price exceeds this burst profile.');
  if(m.phase==='setup'){
    // Native sales increase an existing multiplier but do not renew its time.
    // Allow one second beyond the clicks for the gains frame and the native
    // 33ms loop cadence (buff.time is measured in nominal 30fps ticks).
    const old=o.buffs.Devastation;
    if(old && old.time/o.fps<=config.clicks/config.clickRate+1){
      m.phase='expiry';m.waitUntil=o.elapsedMs+Math.ceil(old.time*1000/o.fps)+100;
      return result('acting','Let the short remaining buff expire before starting a complete burst.',{type:'wait',milliseconds:m.waitUntil-o.elapsedMs});
    }
    m.phase='cycles';m.startedAt=o.elapsedMs;m.startBank=o.cookies;m.startEarned=o.cookiesEarned;
  }
  if(m.phase==='expiry'){
    if(o.elapsedMs<m.waitUntil || o.buffs.Devastation)return result('blocked','The committed native expiry wait did not finish.');
    m.phase='cycles';m.startedAt=o.elapsedMs;m.startBank=o.cookies;m.startEarned=o.cookiesEarned;
  }
  if(m.phase==='cycles'){
    if(o.elapsedMs!==m.startedAt||o.cookiesEarned!==m.startEarned)return result('blocked','An automatic task or earned-cookie change interrupted the same-time prefix.');
    if(m.pending){m.completed+=m.pending;delete m.pending;}
    if(o.cookies<m.startBank-m.lossPerCycle*m.completed)return result('blocked','Native debit exceeded the reserved per-cycle loss.');
    if(m.completed<config.cycles){
      const count=Math.min(config.batchCycles,config.cycles-m.completed);
      if(o.cookies<m.lossPerCycle*count)return result('blocked','The next committed batch is not funded.');
      const actions=[bulk(m.bulkId)];for(let i=0;i<count;i++)actions.push(bulk(1),product,bulk(0),product);
      m.pending=count;
      return result('acting','Execute a finite native sell/rebuy batch without advancing time.',sequence(actions));
    }
    m.phase='gains';return result('acting','Allow a native gains update before the click burst.',{type:'wait',milliseconds:34});
  }
  if(m.phase==='gains'){
    if(!o.buffs.Devastation)return interrupted('The committed buff is absent before the clicks.');
    m.phase='clicks';m.clicksBefore=o.cookieClicks;
    const interval=1000/config.clickRate,actions=[];
    for(let i=0;i<config.clicks;i++)actions.push({type:'wait',milliseconds:interval},{type:'click'});
    return result('acting','Use the native click cadence while the completed buff remains active.',sequence(actions));
  }
  if(m.phase==='clicks'){
    m.phase='complete';m.acceptedClicks=o.cookieClicks-m.clicksBefore;m.afterBank=o.cookies;m.afterEarned=o.cookiesEarned;
    if(m.acceptedClicks!==config.clicks)return interrupted('The native click receipt differs from the committed batch; retain the observed result.');
  }
  return result('complete','The bounded native burst returned; later growth and resets use its actual result.');
})(o,memory,{"clickRate":50,"cycles":16384,"batchCycles":249});}));
    const earlyFundingEnabled = true;
    const lowEffects = true;
    const resetSpells = ((function (observation, actions, memory) {
    return (function resetDecision(o, memory, options) {
  const config = {
    allowReset: false,
    ascensionReady: false,
    collectionStarted: false,
    ...options,
  };
  const m = { ...(memory || {}) };
  const answer = (status, reason, action = null) => ({
    status,
    reason,
    action,
    memory: m,
  });
  const wait = (milliseconds, reason) =>
    answer("acting", reason, { type: "wait", milliseconds });
  const won = (name) => !!o.achievements?.[name];
  const P = o.progression;
  const M = o.controls?.grimoire;
  if (!m.active && won("A wizard is you"))
    return answer("complete", "The native spell achievement is already won.");
  if (!m.active) {
    const achievements = [
      "Hardcore",
      "Neverclick",
      "Reincarnation",
      "No more room in hell",
      "All the stars in heaven",
      "Debt evasion",
      "And a little extra",
      "Speed's the name of the game (no it's not it's called Cookie Clicker)",
      "What's not clicking",
    ];
    const upgrades = ["Legacy", "Starter kit", "Starter kitchen"];
    if (
      !config.allowReset ||
      !config.ascensionReady ||
      config.collectionStarted ||
      !P ||
      P.ascensionMode !== 0 ||
      P.onAscend ||
      P.ascendTimer ||
      P.reincarnateTimer ||
      o.controls?.promptOn ||
      o.controls?.menu ||
      !Number.isFinite(o.prestige) ||
      o.prestige < 2 ** 49 ||
      o.prestige > 2 ** 80 ||
      !Number.isSafeInteger(o.ascensions) ||
      o.ascensions < 100 ||
      !achievements.every(won) ||
      !upgrades.every((name) => o.upgrades?.[name]?.bought) ||
      P.buildingLevels?.["Wizard tower"] !== 1 ||
      !P.minigames?.["Wizard tower"] ||
      !M ||
      !Number.isSafeInteger(M.spellsCastTotal) ||
      M.spellsCastTotal < 0 ||
      M.spellsCastTotal >= 999
    ) {
      return answer(
        "deferred",
        "The scheduler has not released the required funded normal-run boundary.",
      );
    }
    m.active = true;
    m.phase = "ascend";
    m.startCount = M.spellsCastTotal;
    m.completedCasts = 0;
    m.targetCasts = 999 - M.spellsCastTotal;
  }
  if (!config.allowReset)
    return answer(
      "blocked",
      "Reset permission was withdrawn during the spell phase.",
    );
  if (!P || P.ascensionMode !== 0 || !M || o.controls?.promptOn) {
    return answer(
      "blocked",
      "The exclusive normal-run spell phase was interrupted.",
    );
  }
  if (P.ascendTimer > 0) {
    if (!m.escapeSent) {
      m.escapeSent = true;
      return answer("acting", "Finish this ordinary ascension animation.", {
        type: "sequence",
        actions: [
          { type: "key", code: 27, down: true },
          { type: "key", code: 27, down: false },
        ],
      });
    }
    return wait(40, "Allow the native frame to enter heaven.");
  }
  delete m.escapeSent;
  if (P.onAscend) {
    if (P.reincarnateTimer)
      return wait(100, "Finish the current reincarnation.");
    m.phase =
      m.completedCasts === m.targetCasts ? "finish-wait" : "prepare-wait";
    return answer(
      "acting",
      "Restore ordinary reset mana; no heavenly purchase is needed.",
      { type: "reincarnate", mode: 0 },
    );
  }
  if (m.phase === "prepare-wait") {
    m.phase = "prepare";
    return wait(5100, "Wait for the fixed native unlock schedule.");
  }
  if (m.phase === "finish-wait") {
    m.phase = "finish";
    return wait(1100, "Finish the final native reincarnation.");
  }
  if (m.phase === "income-delay") {
    m.phase = "income-wait";
    return wait(200, "Allow native production after prestige activation.");
  }
  if (
    (m.phase === "prepare" ||
      m.phase === "finish" ||
      m.phase === "income-wait") &&
    P.reincarnateTimer
  ) {
    return answer(
      "blocked",
      "The native transition exceeded the stated phase boundary.",
    );
  }
  if (m.phase === "finish") {
    if (
      !won("A wizard is you") ||
      M.spellsCastTotal !== m.startCount + m.targetCasts
    ) {
      return answer(
        "blocked",
        "The completed native casts did not retain their required achievement.",
      );
    }
    m.active = false;
    m.phase = "complete";
    return answer(
      "complete",
      "All required casts and the final normal reincarnation have completed.",
    );
  }
  if (m.phase === "ascend") {
    m.phase = "transition";
    return answer(
      "acting",
      "Start the already selected mana-restoration reset.",
      { type: "ascend" },
    );
  }
  if (m.phase === "prepare") {
    const secret = o.upgrades?.["Heavenly chip secret"];
    const offer = o.shop?.upgrades?.find((u) => u.id === secret?.id);
    if (!secret?.bought) {
      if (!secret?.unlocked || !offer?.canBuy || offer.price > o.cookies) {
        return answer(
          "blocked",
          "The native five-second unlock and starter income did not fund Heavenly chip secret.",
        );
      }
      m.phase = "income-delay";
      return answer(
        "acting",
        "Activate the retained prestige before buying one tower.",
        { type: "buy-upgrade", id: secret.id },
      );
    }
    m.phase = "income-wait";
    return wait(200, "Allow native production after prestige activation.");
  }
  if (m.phase === "income-wait") {
    const tower = o.shop?.buildings?.find((b) => b.name === "Wizard tower");
    if (!tower || tower.amount !== 0 || tower.buy1price > o.cookies) {
      return answer(
        "blocked",
        "The stated starter-income boundary did not fund exactly one tower.",
      );
    }
    m.phase = "open";
    return answer(
      "acting",
      "Buy the one tower required for the ordinary spell control.",
      { type: "buy-building", id: tower.id, amount: 1 },
    );
  }
  if (m.phase === "open") {
    if (M.open !== true) {
      if (M.open !== false)
        return answer(
          "blocked",
          "The rendered Grimoire open state is missing.",
        );
      return answer("acting", "Open the native Grimoire panel.", {
        type: "minigame-open",
        id: 7,
      });
    }
    m.phase = "cast";
  }
  if (m.phase === "cast") {
    if (
      P.buildingAmounts?.["Wizard tower"] !== 1 ||
      M.magicMax !== 5 ||
      M.magic !== 5 ||
      M.spells?.["conjure baked goods"]?.cost !== 4 ||
      M.spellsCastTotal !== m.startCount + m.completedCasts
    ) {
      return answer(
        "blocked",
        "The native reset-mana or persistent-counter boundary changed.",
      );
    }
    m.phase = "count";
    return answer(
      "acting",
      "Make the one selected ordinary cast; its outcome does not change this schedule.",
      { type: "cast-spell", spell: "conjure baked goods" },
    );
  }
  if (m.phase === "count") {
    if (M.spellsCastTotal !== m.startCount + m.completedCasts + 1) {
      return answer(
        "blocked",
        "The ordinary cast did not increment the native persistent counter.",
      );
    }
    m.completedCasts += 1;
    m.phase = "transition";
    return answer(
      "acting",
      "Reset after the selected cast, on either outcome.",
      { type: "ascend" },
    );
  }
  return answer(
    "blocked",
    "The native ascension did not enter its expected transition.",
  );
})(observation, memory, {...{}, ...((memory || {}).config || {})});
  }));
    const setupHelper = ((function(o,actions,memory){return (function helperSetupDecision(o, memory, excluded, count, sweep) {
  const m={...(memory || {})};
  const answer=(status,action=null,reason='')=>({status,action,reason,memory:m});
  if(o.achievements["Baby it's old outside"])return answer('complete');
  if(o.progression.onAscend || o.progression.ascendTimer || o.progression.reincarnateTimer
    || o.progression.ascensionMode!==0 || o.controls.promptOn)return answer('deferred',null,'An active normal run with no prompt is required.');
  if(o.ascensions<1 || !o.upgrades['Season switcher']?.bought)return answer('deferred',null,'Use an already scheduled profitable reset and its Season switcher purchase.');
  if(excluded.some(name=>o.upgrades[name]?.bought))return answer('deferred',null,'This run does not have the certified two-art pool. Keep its scheduled economic reset.');
  if(o.controls.preferences?.animate!==1)return answer('blocked',null,'The pinned helper draw profile requires building animation enabled.');
  if(!Number.isSafeInteger(o.elapsedMs) || o.elapsedMs<0 || o.elapsedMs>2**50)
    return answer('blocked',null,'The pinned Init/Loop-only draw profile does not certify remaining frames at this elapsed time.');
  if(m.attempted)return answer('blocked',null,'The fixed two-art sweep ended without the native achievement. Its display or draw premise is unresolved.');
  const grandma=o.shop.buildings.find(b=>b.name==='Grandma');
  if(!grandma)return answer('blocked',null,'The public Grandma offer is absent.');
  if(grandma.amount<count) {
    if(!grandma.locked && grandma.buy1price<=o.cookies)return answer('acting',{type:'buy-building',id:grandma.id,amount:1});
    return answer('needs-resources',null,'Fund the next of the 24 Grandmas through ordinary growth.');
  }
  if(o.seasonal.season!=='christmas') {
    const offer=o.shop.upgrades.find(u=>u.name==='Festive biscuit' && u.unlocked && !u.bought);
    if(!offer)return answer('blocked',null,'Season switcher has not exposed its native Christmas trigger.');
    if(offer.canBuy && offer.price<=o.cookies)return answer('acting',{type:'buy-upgrade',id:offer.id});
    return answer('needs-resources',null,'Fund the native Christmas trigger through ordinary growth.');
  }
  if(!o.controls.preferences.fancy)return answer('acting',{type:'preference',name:'fancy'});
  const display=o.seasonal.grandmaDisplay;
  if(display?.muted) {
    if(!o.controls.preferences.extraButtons)return answer('acting',{type:'preference',name:'extraButtons'});
    return answer('acting',{type:'building-mute',id:grandma.id,muted:false});
  }
  if(o.controls.menu)return answer('acting',{type:'open-menu',menu:''});
  if(!display || display.width<278 || display.height<89) {
    if(m.resized)return answer('blocked',null,'The configured viewport does not expose the certified 278x89 Grandma rectangle.');
    m.resized=true;
    return answer('acting',{type:'sequence',actions:[{type:'resize',width:1200,height:900},{type:'wait',milliseconds:134}]});
  }
  m.attempted=true;
  return answer('acting',{type:'sequence',actions:sweep});
})(o,memory,["Farmer grandmas","Worker grandmas","Miner grandmas","Cosmic grandmas","Transmuted grandmas","Altered grandmas","Grandmas' grandmas","Antigrandmas","Rainbow grandmas","Banker grandmas","Priestess grandmas","Witch grandmas","Lucky grandmas","Metagrandmas","Script grannies","Alternate grandmas","Brainy grandmas","Clone grandmas"],24,[{"type":"wait","milliseconds":134},{"type":"building-hover","id":1,"x":32,"y":56},{"type":"building-press","id":1,"release":false},{"type":"wait","milliseconds":134},{"type":"building-press","id":1,"release":true},{"type":"building-hover","id":1,"x":42,"y":72},{"type":"building-press","id":1,"release":false},{"type":"wait","milliseconds":134},{"type":"building-press","id":1,"release":true},{"type":"building-hover","id":1,"x":53,"y":88},{"type":"building-press","id":1,"release":false},{"type":"wait","milliseconds":134},{"type":"building-press","id":1,"release":true},{"type":"building-hover","id":1,"x":64,"y":56},{"type":"building-press","id":1,"release":false},{"type":"wait","milliseconds":134},{"type":"building-press","id":1,"release":true},{"type":"building-hover","id":1,"x":74,"y":72},{"type":"building-press","id":1,"release":false},{"type":"wait","milliseconds":134},{"type":"building-press","id":1,"release":true},{"type":"building-hover","id":1,"x":85,"y":88},{"type":"building-press","id":1,"release":false},{"type":"wait","milliseconds":134},{"type":"building-press","id":1,"release":true},{"type":"building-hover","id":1,"x":96,"y":56},{"type":"building-press","id":1,"release":false},{"type":"wait","milliseconds":134},{"type":"building-press","id":1,"release":true},{"type":"building-hover","id":1,"x":106,"y":72},{"type":"building-press","id":1,"release":false},{"type":"wait","milliseconds":134},{"type":"building-press","id":1,"release":true},{"type":"building-hover","id":1,"x":117,"y":88},{"type":"building-press","id":1,"release":false},{"type":"wait","milliseconds":134},{"type":"building-press","id":1,"release":true},{"type":"building-hover","id":1,"x":128,"y":56},{"type":"building-press","id":1,"release":false},{"type":"wait","milliseconds":134},{"type":"building-press","id":1,"release":true},{"type":"building-hover","id":1,"x":138,"y":72},{"type":"building-press","id":1,"release":false},{"type":"wait","milliseconds":134},{"type":"building-press","id":1,"release":true},{"type":"building-hover","id":1,"x":149,"y":88},{"type":"building-press","id":1,"release":false},{"type":"wait","milliseconds":134},{"type":"building-press","id":1,"release":true},{"type":"building-hover","id":1,"x":160,"y":56},{"type":"building-press","id":1,"release":false},{"type":"wait","milliseconds":134},{"type":"building-press","id":1,"release":true},{"type":"building-hover","id":1,"x":170,"y":72},{"type":"building-press","id":1,"release":false},{"type":"wait","milliseconds":134},{"type":"building-press","id":1,"release":true},{"type":"building-hover","id":1,"x":181,"y":88},{"type":"building-press","id":1,"release":false},{"type":"wait","milliseconds":134},{"type":"building-press","id":1,"release":true},{"type":"building-hover","id":1,"x":192,"y":56},{"type":"building-press","id":1,"release":false},{"type":"wait","milliseconds":134},{"type":"building-press","id":1,"release":true},{"type":"building-hover","id":1,"x":202,"y":72},{"type":"building-press","id":1,"release":false},{"type":"wait","milliseconds":134},{"type":"building-press","id":1,"release":true},{"type":"building-hover","id":1,"x":213,"y":88},{"type":"building-press","id":1,"release":false},{"type":"wait","milliseconds":134},{"type":"building-press","id":1,"release":true},{"type":"building-hover","id":1,"x":224,"y":56},{"type":"building-press","id":1,"release":false},{"type":"wait","milliseconds":134},{"type":"building-press","id":1,"release":true},{"type":"building-hover","id":1,"x":234,"y":72},{"type":"building-press","id":1,"release":false},{"type":"wait","milliseconds":134},{"type":"building-press","id":1,"release":true},{"type":"building-hover","id":1,"x":245,"y":88},{"type":"building-press","id":1,"release":false},{"type":"wait","milliseconds":134},{"type":"building-press","id":1,"release":true},{"type":"building-hover","id":1,"x":256,"y":56},{"type":"building-press","id":1,"release":false},{"type":"wait","milliseconds":134},{"type":"building-press","id":1,"release":true},{"type":"building-hover","id":1,"x":266,"y":72},{"type":"building-press","id":1,"release":false},{"type":"wait","milliseconds":134},{"type":"building-press","id":1,"release":true},{"type":"building-hover","id":1,"x":277,"y":88},{"type":"building-press","id":1,"release":false},{"type":"wait","milliseconds":134},{"type":"building-press","id":1,"release":true}]);}));
    const helperSetupEnabled = true;
    const helperArtExclusions = ["Farmer grandmas","Worker grandmas","Miner grandmas","Cosmic grandmas","Transmuted grandmas","Altered grandmas","Grandmas' grandmas","Antigrandmas","Rainbow grandmas","Banker grandmas","Priestess grandmas","Witch grandmas","Lucky grandmas","Metagrandmas","Script grannies","Alternate grandmas","Brainy grandmas","Clone grandmas"];
    const spellResetEnabled = true;
    const resetPermission = true;
    const earlyCountDefault = true;
    const withholdActivation = false;
    const activationNames=['Heavenly chip secret','Heavenly cookie stand','Heavenly bakery','Heavenly confectionery','Heavenly key'];
    const clickRate = 50;
    const normalNames = ["Wake and bake","Making some dough","So baked right now","Fledgling bakery","Affluent bakery","World-famous bakery","Cosmic bakery","Galactic bakery","Universal bakery","Timeless bakery","Infinite bakery","Immortal bakery","Don't stop me now","You can stop now","Cookies all the way down","Overdose","Casual baking","Hardcore baking","Steady tasty stream","Cookie monster","Mass producer","Cookie vortex","Cookie pulsar","Cookie quasar","Oh hey, you're still here","Let's never bake again","Sacrifice","Oblivion","From scratch","Neverclick","Clicktastic","Clickathlon","Clickolympics","Clickorama","Click","Double-click","Mouse wheel","Of Mice and Men","The Digital","Just wrong","Grandma's cookies","Sloppy kisses","Retirement home","Bought the farm","Reap what you sow","Farm ill","Production chain","Industrial revolution","Global warming","You know the drill","Excavation site","Hollow the planet","Expedition","Galactic highway","Far far away","Transmutation","Transmogrification","Gold member","A whole new world","Now you're thinking","Dimensional shift","Time warp","Alternate timeline","Rewriting history","One with everything","Mathematician","Base 10","Golden cookie","Lucky cookie","A stroke of luck","Uncanny clicker","Builder","Architect","Enhancer","Augmenter","Cookie-dunker","Fortune","Elder nap","Elder slumber","Elder","Elder calm","Engineer","Leprechaun","Black cat's paw","Nihilism","Antibatter","Quirky quarks","It does matter!","Upgrader","Centennial","Hardcore","Clickasmic","Friend of the ancients","Ruler of the ancients","Wholesome","Itchscratcher","Wrinklesquisher","Moistburster","Spooky cookies","Coming to town","All hail Santa","Let it snow","Oh deer","Sleigh of hand","Reindeer sleigher","Perfected agriculture","Ultimate automation","Can you dig it","Type II civilization","Gild wars","Brain-split","Time duke","Molecular maestro","Lone photon","Dazzling glimmer","Blinding flash","Unending glow","Lord of Constructs","Lord of Progress","Bicentennial","Lovely cookies","Centennial and a half","Tiny cookie","You win a cookie","Click delegator","Gushing grannies","I hate manure","Never dig down","The incredible machine","And beyond","Magnum Opus","With strange eons","Spacetime jigamaroo","Supermassive","Praise the sun","Clickageddon","Clicknarok","Extreme polydactyly","Dr. T","The old never bothered me anyway","Homegrown","Technocracy","The center of the Earth","We come in peace","The secrets of the universe","Realm of the Mad God","Forever and ever","Walk the planck","Rise and shine","Dematerialize","Nil zero zilch","Transcendence","Obliterate","Negative void","The hunt is on","Egging on","Mass Easteria","Hide & seek champion","What's in a name","Pretty penny","Fit the bill","A loan in the dark","Need for greed","It's the economy, stupid","Your time to shrine","Shady sect","New-age cult","Organized religion","Fanaticism","Bewitched","The sorcerer's apprentice","Charms and enchantments","Curses and maledictions","Magic kingdom","Vested interest","New world order","Hocus pocus","Finger clickin' good","Panic at the bingo","Rake in the dough","Quarry on","Yes I love technology","Paid in full","Church of Cookiology","Too many rabbits, not enough hats","The most precious cargo","The Aureate","Ever more hideous","Be kind, rewind","Infinitesimal","A still more glorious dawn","Rebirth","Here you go","Resurrection","Reincarnation","The agemaster","To oldly go","Gardener extraordinaire","Tectonic ambassador","Rise of the machines","Acquire currency","Zealotry","The wizarding world","Parsec-masher","The work of a lifetime","A place lost in time","Heat death","Microcosm","Bright future","Here be dragon","How?","The land of milk and cookies","He who controls the cookies controls the universe","Tonight on Hoarders","Are you gonna eat all that?","We're gonna need a bigger bakery","In the mouth of madness","Brought to you by the letter <div style=\"display:inline-block;background:url(img/money.png);width:16px;height:16px;\"></div>","A world filled with cookies","When this baby hits 36 quadrillion cookies per hour","Fast and delicious","Cookiehertz : a really, really tasty hertz","Woops, you solved world hunger","Turbopuns","Faster menner","And yet you're still hungry","The Abakening","There's really no hard limit to how long these achievement names can be and to be quite honest I'm rather curious to see how far we can go.<br>Adolphus W. Green (1844–1917) started as the Principal of the Groton School in 1864. By 1865, he became second assistant librarian at the New York Mercantile Library; from 1867 to 1869, he was promoted to full librarian. From 1869 to 1873, he worked for Evarts, Southmayd & Choate, a law firm co-founded by William M. Evarts, Charles Ferdinand Southmayd and Joseph Hodges Choate. He was admitted to the New York State Bar Association in 1873.<br>Anyway, how's your day been?","Fast","Bicentennial and a half","Tabloid addiction","Clickastrophe","Clickataclysm","Thumbs, phalanges, metacarpals","Polymath","The elder scrolls","To crumbs, you say?","Seedy business","Freak fracking","Modern times","The nerve of war","Wololo","And now for my next trick, I'll need a volunteer from the audience","It's not delivery","Gold, Jerry! Gold!","Forbidden zone","cookie clicker forever and forever a hundred years cookie clicker, all day long forever, forever a hundred times, over and over cookie clicker adventures dot com","Scientists baffled everywhere","Harmony of the spheres","Early bird","Fading luck","Eldeer","Dude, sweet","Sugar rush","Year's worth of cavities","Hand-picked","Sugar sugar","Sweetmeats","Tricentennial","Knead for speed","Well the cookies start coming and they don't stop coming","I don't know if you've noticed but all these icons are very slightly off-center","The proof of the cookie is in the baking","If it's worth doing, it's worth overdoing","The dreams in which I'm baking are the best I've ever had","Set for life","You and the beanstalk","Romancing the stone","Ex machina","And I need it now","Pray on the weak","It's a kind of magic","Make it so","All that glitters is gold","H̸̷͓̳̳̯̟͕̟͍͍̣͡ḛ̢̦̰̺̮̝͖͖̘̪͉͘͡ ̠̦͕̤̪̝̥̰̠̫̖̣͙̬͘ͅC̨̦̺̩̲̥͉̭͚̜̻̝̣̼͙̮̯̪o̴̡͇̘͎̞̲͇̦̲͞͡m̸̩̺̝̣̹̱͚̬̥̫̳̼̞̘̯͘ͅẹ͇̺̜́̕͢s̶̙̟̱̥̮̯̰̦͓͇͖͖̝͘͘͞","Way back then","Exotic matter","At the end of the tunnel","Click (starring Adam Sandler)","Frantiquities","Overgrowth","Sedimentalism","Labor of love","Reverse funnel system","Thus spoke you","Manafest destiny","Neither snow nor rain nor heat nor gloom of night","I've got the Midas touch","Which eternal lie","D&eacute;j&agrave; vu","Powers of Ten","Now the dark days are gone","Freaky jazz hands","Methuselah","Huge tracts of land","D-d-d-d-deeper","Patently genius","A capital idea","It belongs in a bakery","Motormouth","Been there done that","Phlogisticated substances","Bizarro world","The long now","Chubby hadrons","Palettable","Bibbidi-bobbidi-boo","I'm the wiz","A wizard is you","Lucked out","What are the odds","Grandma needs a new pair of shoes","Million to one shot, doc","As luck would have it","Ever in your favor","Be a lady","Dicey business","Fingers crossed","Just a statistic","Murphy's wild guess","Let's leaf it at that","The ultimate clickdown","Aged well","101st birthday","But wait 'til you get older","Harvest moon","Mine?","In full gear","Treacle tart economics","Holy cookies, grandma!","The Prestige","That's just peanuts to space","Worth its weight in lead","What happens in the vortex stays in the vortex","Invited to yesterday's party","Downsizing","My eyes","Maybe a chance in hell, actually","Make like a tree","Cave story","In-cog-neato","Save your breath because that's all you've got left","Vengeful and almighty","Spell it out for you","Space space space space space","Don't get used to yourself, you're gonna have to change","Objects in the mirror dimension are closer than they appear","Groundhog day","A matter of perspective","Optical illusion","Jackpot","Running with scissors","Rarefied air","Push it to the limit","Green cookies sleep furiously","Panic! at Nabisco","Bursting at the seams","Just about full","Hungry for more","All the other kids with the pumped up clicks","One...more...click...","Botany enthusiast","Green, aching thumb","In the garden of Eden (baby)","Keeper of the conservatory","Seedless to nay","You get nothing","Humble rebeginnings","The end of the world","Oh, you're back","Lazarus","Leisurely pace","Hypersonic","Feed me, Orteil","And then what?","Tricentennial and a half","Quadricentennial","Quadricentennial and a half","Quincentennial","Maillard reaction","With her finger and her thumb","Defense of the ancients","Sharpest tool in the shed","Hey now, you're a rock","Break the mold","Get the show on, get paid","My world's on fire, how about yours","The meteor men beg to differ","Only shooting stars","We could all use a little change","Your brain gets smart but your head gets dumb","The years start coming","What a concept","You'll never shine if you don't glow","You'll never know if you don't go","Self-contained","Threw you for a loop","The sum of its parts","Bears repeating","More of the same","Last recurse","Out of one, many","An example of recursion","For more information on this achievement, please refer to its title","I'm so meta, even this achievement","Never get bored","The needs of the many","Eating its own","We must go deeper","Sierpinski rhomboids","Gotta go fast","I think it's safe to say you've got it made","Renaissance baker","Veteran","Thick-skinned","F12","Variable success","No comments","Up to code","Works on my machine","Technical debt","Mind your language","Inconsolable","Closure","Dude what if we're all living in a simulation like what if we're all just code on a computer somewhere","Taking the back streets","Inherited prototype","A model of document object","First-class citizen","Alexandria","Bake him away, toys","You're #1 so why try harder","Haven't even begun to peak","A sometimes food","Not enough of a good thing","Horn of plenty","Smurf account","If at first you don't succeed","O Fortuna","Initial public offering","Rookie numbers","No nobility in poverty","Full warehouses","Make my day","Buy buy buy","Pyramid scheme","Jellicles","Quincentennial and a half","What did we even eat before these","Heavy flow","More you say?","Large and in charge","Absolutely stuffed","It's only wafer-thin","Clickety split","Gotta hand it to you","Okay boomer","Overripe","Rock on","Self-manmade man","Checks out","Living on a prayer","Higitus figitus migitus mum","The incredible journey","Just a phase","Don't let me leave, Murph","Caveman to cosmos","Particular tastes","A light snack","Tempting fate","Tautological","Curly braces","Olden days","The devil's workshop","In the green","Mountain out of a molehill, but like in a good way","The wheels of progress","That's rich","Preaches and cream","Magic thinking","Is there life on Mars?","Bad chemistry","Reduced to gibbering heaps","Back already?","Nuclear throne","Making light of the situation","Flip a cookie. Chips, I win. Crust, you lose.","In and of itself","Duck typing","They'll never know what hit 'em","Well-versed","Ripe for the picking","Unreal","Once you've seen one","Spoils and plunder","Nobody exists on purpose, nobody belongs anywhere","Hyperspace expressway","Versatile","You are inevitable","Away from this place","Everywhere at once","Reject reality, substitute your own","Fringe","Coherence","Earth-616","Strange topologies","Grand design","Ecumenopolis","The full picture","When there's nothing left to add","Sexcentennial","Keep going until I say stop","But I didn't say stop, did I?","With unrivaled fervor","Think big","Hypersize me","Max capacity","Liquid assets","Stifling the press","It's big brain time","Just my imagination","Now there's an idea","The organ that named itself","Gyrification","A trademarked portmanteau of \"imagination\" and \"engineering\"","Mindfulness","The 10% myth","Don't think about it too hard","Though fools seldom differ","Looking kind of dumb","A beautiful mind","Cardinal synapses","Positive thinking","The thought that counts","Unthinkable","Gifted","They moistly come at night","It's grown on you","Don't let the walls cave in on you","Replaced by robots","Financial prodigy","And I will pray to a big god","Shosple Colupis","False vacuum","Metallic taste","Swiss cheese","But the future refused to change","What's the dark matter with you","Enlightenment","Never tell me the odds","Blowing an Apollonian gasket","Get with the program","Lost your cosmic marbles","By will alone I set my mind in motion","Ain't that a click in the head","Sexcentennial and a half","I am speed","And on and on","Fake it till you bake it","History in the baking","Baby it's old outside","Myriad","Kaizen","Beyond quality","Everything happens so much","I'll rest when I'm dead","What do you get for the baker who has everything","Bottomless pit","All the stars in heaven","No time like the present","Can we get much higher","Speed's the name of the game (no it's not it's called Cookie Clicker)","Rainy day fund","And a little extra","Grandmapocalypse","Wrath cookie","No more room in hell","Wrinkler poker","Septcentennial","My own clone","Multiplicity","Born for this job","Episode II","Copy that","Life finds a way","Overcrowding","Strength in numbers","Army of me","Know thyself","Didn't make sense not to live","Genetic bottleneck","Despite everything, it's still you","Everyone everywhere all at once","Self-made","Reproducible results","That's all you","Self-improvement","And now you're even older","Au naturel","Dirt-rich","Bots build bots","Getting that bag","The leader is good, the leader is great","You don't think they could've used... it couldn't have been ma-","Signed, sealed, delivered","Sugar, spice, and everything nice","Not even remotely close to Kansas anymore","I only meant to stay a while","Not 20 years away forever","Bright side of the Moon","Riding the Mersenne twister","Divide and conquer","Pebcakes","Greener on the other sides","Where is my mind","Introspection","Debt evasion","Oft we mar what's well","Cookie Clicker","What's not clicking","All on deck","A round of applause"];
    const requiredNames = ["Wake and bake","Making some dough","So baked right now","Fledgling bakery","Affluent bakery","World-famous bakery","Cosmic bakery","Galactic bakery","Universal bakery","Timeless bakery","Infinite bakery","Immortal bakery","Don't stop me now","You can stop now","Cookies all the way down","Overdose","Casual baking","Hardcore baking","Steady tasty stream","Cookie monster","Mass producer","Cookie vortex","Cookie pulsar","Cookie quasar","Oh hey, you're still here","Let's never bake again","Sacrifice","Oblivion","From scratch","Neverclick","Clicktastic","Clickathlon","Clickolympics","Clickorama","Click","Double-click","Mouse wheel","Of Mice and Men","The Digital","Just wrong","Grandma's cookies","Sloppy kisses","Retirement home","Bought the farm","Reap what you sow","Farm ill","Production chain","Industrial revolution","Global warming","You know the drill","Excavation site","Hollow the planet","Expedition","Galactic highway","Far far away","Transmutation","Transmogrification","Gold member","A whole new world","Now you're thinking","Dimensional shift","Time warp","Alternate timeline","Rewriting history","One with everything","Mathematician","Base 10","Golden cookie","Lucky cookie","A stroke of luck","Uncanny clicker","Builder","Architect","Enhancer","Augmenter","Cookie-dunker","Fortune","Elder nap","Elder slumber","Elder","Elder calm","Engineer","Leprechaun","Black cat's paw","Nihilism","Antibatter","Quirky quarks","It does matter!","Upgrader","Centennial","Hardcore","Clickasmic","Friend of the ancients","Ruler of the ancients","Wholesome","Itchscratcher","Wrinklesquisher","Moistburster","Spooky cookies","Coming to town","All hail Santa","Let it snow","Oh deer","Sleigh of hand","Reindeer sleigher","Perfected agriculture","Ultimate automation","Can you dig it","Type II civilization","Gild wars","Brain-split","Time duke","Molecular maestro","Lone photon","Dazzling glimmer","Blinding flash","Unending glow","Lord of Constructs","Lord of Progress","Bicentennial","Lovely cookies","Centennial and a half","Tiny cookie","You win a cookie","Click delegator","Gushing grannies","I hate manure","Never dig down","The incredible machine","And beyond","Magnum Opus","With strange eons","Spacetime jigamaroo","Supermassive","Praise the sun","Clickageddon","Clicknarok","Extreme polydactyly","Dr. T","The old never bothered me anyway","Homegrown","Technocracy","The center of the Earth","We come in peace","The secrets of the universe","Realm of the Mad God","Forever and ever","Walk the planck","Rise and shine","Dematerialize","Nil zero zilch","Transcendence","Obliterate","Negative void","The hunt is on","Egging on","Mass Easteria","Hide & seek champion","What's in a name","Pretty penny","Fit the bill","A loan in the dark","Need for greed","It's the economy, stupid","Your time to shrine","Shady sect","New-age cult","Organized religion","Fanaticism","Bewitched","The sorcerer's apprentice","Charms and enchantments","Curses and maledictions","Magic kingdom","Vested interest","New world order","Hocus pocus","Finger clickin' good","Panic at the bingo","Rake in the dough","Quarry on","Yes I love technology","Paid in full","Church of Cookiology","Too many rabbits, not enough hats","The most precious cargo","The Aureate","Ever more hideous","Be kind, rewind","Infinitesimal","A still more glorious dawn","Rebirth","Here you go","Resurrection","Reincarnation","The agemaster","To oldly go","Gardener extraordinaire","Tectonic ambassador","Rise of the machines","Acquire currency","Zealotry","The wizarding world","Parsec-masher","The work of a lifetime","A place lost in time","Heat death","Microcosm","Bright future","Here be dragon","How?","The land of milk and cookies","He who controls the cookies controls the universe","Tonight on Hoarders","Are you gonna eat all that?","We're gonna need a bigger bakery","In the mouth of madness","Brought to you by the letter <div style=\"display:inline-block;background:url(img/money.png);width:16px;height:16px;\"></div>","A world filled with cookies","When this baby hits 36 quadrillion cookies per hour","Fast and delicious","Cookiehertz : a really, really tasty hertz","Woops, you solved world hunger","Turbopuns","Faster menner","And yet you're still hungry","The Abakening","There's really no hard limit to how long these achievement names can be and to be quite honest I'm rather curious to see how far we can go.<br>Adolphus W. Green (1844–1917) started as the Principal of the Groton School in 1864. By 1865, he became second assistant librarian at the New York Mercantile Library; from 1867 to 1869, he was promoted to full librarian. From 1869 to 1873, he worked for Evarts, Southmayd & Choate, a law firm co-founded by William M. Evarts, Charles Ferdinand Southmayd and Joseph Hodges Choate. He was admitted to the New York State Bar Association in 1873.<br>Anyway, how's your day been?","Fast","Bicentennial and a half","Tabloid addiction","Clickastrophe","Clickataclysm","Thumbs, phalanges, metacarpals","Polymath","The elder scrolls","To crumbs, you say?","Seedy business","Freak fracking","Modern times","The nerve of war","Wololo","And now for my next trick, I'll need a volunteer from the audience","It's not delivery","Gold, Jerry! Gold!","Forbidden zone","cookie clicker forever and forever a hundred years cookie clicker, all day long forever, forever a hundred times, over and over cookie clicker adventures dot com","Scientists baffled everywhere","Harmony of the spheres","Early bird","Fading luck","Eldeer","Dude, sweet","Sugar rush","Hand-picked","Tricentennial","Knead for speed","Well the cookies start coming and they don't stop coming","I don't know if you've noticed but all these icons are very slightly off-center","The proof of the cookie is in the baking","If it's worth doing, it's worth overdoing","The dreams in which I'm baking are the best I've ever had","Set for life","You and the beanstalk","Romancing the stone","Ex machina","And I need it now","Pray on the weak","It's a kind of magic","Make it so","All that glitters is gold","H̸̷͓̳̳̯̟͕̟͍͍̣͡ḛ̢̦̰̺̮̝͖͖̘̪͉͘͡ ̠̦͕̤̪̝̥̰̠̫̖̣͙̬͘ͅC̨̦̺̩̲̥͉̭͚̜̻̝̣̼͙̮̯̪o̴̡͇̘͎̞̲͇̦̲͞͡m̸̩̺̝̣̹̱͚̬̥̫̳̼̞̘̯͘ͅẹ͇̺̜́̕͢s̶̙̟̱̥̮̯̰̦͓͇͖͖̝͘͘͞","Way back then","Exotic matter","At the end of the tunnel","Click (starring Adam Sandler)","Frantiquities","Overgrowth","Sedimentalism","Labor of love","Reverse funnel system","Thus spoke you","Manafest destiny","Neither snow nor rain nor heat nor gloom of night","I've got the Midas touch","Which eternal lie","D&eacute;j&agrave; vu","Powers of Ten","Now the dark days are gone","Bibbidi-bobbidi-boo","I'm the wiz","A wizard is you","Lucked out","What are the odds","Grandma needs a new pair of shoes","Million to one shot, doc","As luck would have it","Ever in your favor","Be a lady","Dicey business","Fingers crossed","Just a statistic","Murphy's wild guess","The ultimate clickdown","Aged well","101st birthday","But wait 'til you get older","Harvest moon","Mine?","In full gear","Treacle tart economics","Holy cookies, grandma!","The Prestige","That's just peanuts to space","Worth its weight in lead","What happens in the vortex stays in the vortex","Invited to yesterday's party","Downsizing","My eyes","Maybe a chance in hell, actually","Make like a tree","Cave story","In-cog-neato","Save your breath because that's all you've got left","Vengeful and almighty","Spell it out for you","Space space space space space","Don't get used to yourself, you're gonna have to change","Objects in the mirror dimension are closer than they appear","Groundhog day","A matter of perspective","Optical illusion","Jackpot","Running with scissors","Rarefied air","Push it to the limit","Green cookies sleep furiously","Panic! at Nabisco","Bursting at the seams","Just about full","Hungry for more","All the other kids with the pumped up clicks","One...more...click...","Botany enthusiast","Green, aching thumb","In the garden of Eden (baby)","Keeper of the conservatory","Seedless to nay","You get nothing","Humble rebeginnings","The end of the world","Oh, you're back","Lazarus","Leisurely pace","Hypersonic","Feed me, Orteil","And then what?","Tricentennial and a half","Quadricentennial","Quadricentennial and a half","Quincentennial","With her finger and her thumb","Defense of the ancients","Sharpest tool in the shed","Hey now, you're a rock","Break the mold","Get the show on, get paid","My world's on fire, how about yours","The meteor men beg to differ","Only shooting stars","We could all use a little change","Your brain gets smart but your head gets dumb","The years start coming","What a concept","You'll never shine if you don't glow","You'll never know if you don't go","Self-contained","Threw you for a loop","The sum of its parts","Bears repeating","More of the same","Last recurse","Out of one, many","An example of recursion","For more information on this achievement, please refer to its title","I'm so meta, even this achievement","Never get bored","The needs of the many","Eating its own","We must go deeper","Gotta go fast","I think it's safe to say you've got it made","Renaissance baker","Veteran","Thick-skinned","F12","Variable success","No comments","Up to code","Works on my machine","Technical debt","Mind your language","Inconsolable","Closure","Dude what if we're all living in a simulation like what if we're all just code on a computer somewhere","Taking the back streets","Inherited prototype","A model of document object","First-class citizen","Bake him away, toys","You're #1 so why try harder","Haven't even begun to peak","A sometimes food","Not enough of a good thing","Horn of plenty","Smurf account","If at first you don't succeed","O Fortuna","Initial public offering","Rookie numbers","No nobility in poverty","Full warehouses","Make my day","Buy buy buy","Pyramid scheme","Jellicles","Quincentennial and a half","What did we even eat before these","Heavy flow","More you say?","Large and in charge","Absolutely stuffed","It's only wafer-thin","Clickety split","Gotta hand it to you","Okay boomer","Overripe","Rock on","Self-manmade man","Checks out","Living on a prayer","Higitus figitus migitus mum","The incredible journey","Just a phase","Don't let me leave, Murph","Caveman to cosmos","Particular tastes","A light snack","Tempting fate","Tautological","Curly braces","Olden days","The devil's workshop","In the green","Mountain out of a molehill, but like in a good way","The wheels of progress","That's rich","Preaches and cream","Magic thinking","Is there life on Mars?","Bad chemistry","Reduced to gibbering heaps","Back already?","Nuclear throne","Making light of the situation","Flip a cookie. Chips, I win. Crust, you lose.","In and of itself","Duck typing","They'll never know what hit 'em","Well-versed","Ripe for the picking","Unreal","Once you've seen one","Spoils and plunder","Nobody exists on purpose, nobody belongs anywhere","Hyperspace expressway","Versatile","You are inevitable","Away from this place","Everywhere at once","Reject reality, substitute your own","Fringe","Coherence","Earth-616","Grand design","Ecumenopolis","The full picture","When there's nothing left to add","Sexcentennial","Keep going until I say stop","But I didn't say stop, did I?","With unrivaled fervor","Think big","Hypersize me","Max capacity","Liquid assets","Stifling the press","It's big brain time","Just my imagination","Now there's an idea","The organ that named itself","Gyrification","A trademarked portmanteau of \"imagination\" and \"engineering\"","Mindfulness","The 10% myth","Don't think about it too hard","Though fools seldom differ","Looking kind of dumb","A beautiful mind","Cardinal synapses","Positive thinking","The thought that counts","Unthinkable","They moistly come at night","It's grown on you","Don't let the walls cave in on you","Replaced by robots","Financial prodigy","And I will pray to a big god","Shosple Colupis","False vacuum","Metallic taste","Swiss cheese","But the future refused to change","What's the dark matter with you","Enlightenment","Never tell me the odds","Blowing an Apollonian gasket","Get with the program","Lost your cosmic marbles","By will alone I set my mind in motion","Ain't that a click in the head","Sexcentennial and a half","I am speed","And on and on","Fake it till you bake it","History in the baking","Baby it's old outside","Myriad","Kaizen","Beyond quality","Everything happens so much","I'll rest when I'm dead","What do you get for the baker who has everything","Bottomless pit","All the stars in heaven","No time like the present","Can we get much higher","Speed's the name of the game (no it's not it's called Cookie Clicker)","Rainy day fund","And a little extra","Grandmapocalypse","Wrath cookie","No more room in hell","Wrinkler poker","Septcentennial","My own clone","Multiplicity","Born for this job","Episode II","Copy that","Life finds a way","Overcrowding","Strength in numbers","Army of me","Know thyself","Didn't make sense not to live","Genetic bottleneck","Despite everything, it's still you","Everyone everywhere all at once","Self-made","Reproducible results","That's all you","And now you're even older","Au naturel","Dirt-rich","Bots build bots","Getting that bag","The leader is good, the leader is great","You don't think they could've used... it couldn't have been ma-","Signed, sealed, delivered","Sugar, spice, and everything nice","Not even remotely close to Kansas anymore","I only meant to stay a while","Not 20 years away forever","Bright side of the Moon","Riding the Mersenne twister","Divide and conquer","Pebcakes","Greener on the other sides","Where is my mind","Introspection","Debt evasion","Oft we mar what's well","Cookie Clicker","What's not clicking","All on deck","A round of applause"];
    const preserveChallenges = true;
    const farmSugar = true;
    const collectTradesOverride = null;
    const minimumSacrifices = 1;
    const naturalCookieFarm = true;
    return function (o, actions, memory) {
      const m = { ...(memory || {}) };
      const earlyCountPhase=(m.ascension?.config?.allowReset ?? resetPermission)
        && (m.ascension?.config?.earlyCountResets ?? earlyCountDefault) && o.ascensions<100;
      // Optional diagnostic restriction for the older zero-prestige-effect profile.
      // Native profitable-reset and Lucky conditions do not require this hold.
      if(earlyCountPhase && withholdActivation)o={...o,shop:{...o.shop,upgrades:o.shop.upgrades.filter(u=>!activationNames.includes(u.name))}};
      // The exhaustive helper certificate has exactly two Christmas artworks.
      // Preserve that pool, including across permanent-slot assignments.
      const needHelperSetup=helperSetupEnabled && !m.spellReset?.active && (m.season?.config?.helperGrandma ?? true) && !o.achievements["Baby it's old outside"];
      if(needHelperSetup)o={...o,shop:{...o.shop,upgrades:o.shop.upgrades.filter(u=>!helperArtExclusions.includes(u.name))},
        ascension:{...o.ascension,permanentCandidates:(o.ascension.permanentCandidates || []).filter(u=>!helperArtExclusions.includes(u.name))}};
      const answer = (action, stage) => {
        let at=o.elapsedMs,lastClick=null;
        for(const input of action.type==='sequence' ? action.actions : [action]) {
          if(input.type==='wait')at+=input.milliseconds;
          if(input.type==='click')lastClick=at;
        }
        if(lastClick!==null && clickRate>0) {
          const next=lastClick+1000/clickRate;
          if(m.growth)m.growth={...m.growth,nextClick:next};
          if(m.combo)m.combo={...m.combo,nextClickAt:next};
          if(m.production)m.production={...m.production,nextClickAt:next};
        }
        return {action, memory:m, stage, optimalityCertified:false};
      };
      const wait = (milliseconds, stage) => answer({type:'wait',milliseconds},stage);
      const runFunding = (reserve=0) => {
        if(!m.earlyFunding?.phase)m.fundingReserve=reserve;
        const view={...o,cookies:Math.max(0,o.cookies-(m.fundingReserve||0))};
        const decision=fund(view,actions,m.earlyFunding);m.earlyFunding=decision.memory;
        if(decision.status==='blocked')throw new Error('Early funding source boundary: '+decision.reason);
        if(decision.action)return answer(decision.action,'early-income-burst');
        if(decision.status==='complete'||decision.status==='interrupted'){
          delete m.earlyFunding;delete m.fundingReserve;m.nextFundingAt=o.elapsedMs+1000;
          if(m.growth)m.growth={...m.growth,nextPurchase:o.elapsedMs};
          // A current-save reload may discard inputs and restore the original
          // buff arguments. Retain its actual state and give restoration time.
          if(decision.status==='interrupted')return wait(1000,'early-income-interrupted');
        }
        return null;
      };
      const runSpellReset = () => {
        const state={...(m.spellReset || {}),config:{allowReset:spellResetEnabled && resetPermission && (m.ascension?.config?.allowReset ?? true),
          ascensionReady:true,collectionStarted:!!m.finalCollectionStarted}};
        const decision=resetSpells(o,actions,state);m.spellReset=decision.memory;
        if(decision.status==='blocked')throw new Error('Spell-reset source boundary: '+decision.reason);
        return decision.action ? answer(decision.action,'spell-count-resets') : null;
      };
      const p = o.progression;
      // The next burst returns Cursors to its fixed batch. Invest ordinary
      // growth in other buildings while that income phase is available.
      const growthBuildings = () => earlyFundingEnabled && !m.finalCollectionStarted && p.minigames.Temple
        && o.controls.pantheon?.slots?.[0]===2 && o.upgrades['Plastic mouse']?.bought
        && o.shop.buildings.some(b=>b.name==='Temple'&&b.amount>0)
        ? o.shop.buildings.map(b=>b.id===0?{...b,locked:true}:b) : o.shop.buildings;
      const inTransition=!!(p.onAscend || p.ascendTimer || p.reincarnateTimer);
      // A fresh maintenance realm can expose its initial values before loading
      // the current save. Ordinary resets retain these observed milestones.
      if ((m.run!==undefined && o.ascensions<m.run) || (m.hardcoreObserved && !o.achievements.Hardcore))
        return wait(1000,'current-save-restoration');
      m.hardcoreObserved=!!(m.hardcoreObserved || o.achievements.Hardcore);
      // Reincarnation resets current-run control state, but not achievements,
      // building levels, or the seed log. Never carry a stale prompt owner.
      if ((m.run !== undefined && m.run !== o.ascensions) || (m.wasInTransition && !inTransition)) {
        delete m.garden; delete m.market; delete m.season; delete m.growth; delete m.misc; delete m.production; delete m.combo;
        delete m.confirmOneMind;delete m.nextHelperBuilding;delete m.helperSetup;delete m.earlyFunding;delete m.nextFundingAt;delete m.fundingReserve;
      }
      m.run = o.ascensions;
      m.wasInTransition=inTransition;
      // Once selected, this phase owns every action through its final reset.
      // It observes count progress, but never chooses a schedule from spell outcomes.
      if(m.spellReset?.active) {
        const decision=runSpellReset();if(decision)return decision;
      }
      if (p.onAscend || p.ascendTimer || p.reincarnateTimer) {
        const decision = ascend(o,actions,m.ascension); m.ascension=decision.memory;
        return decision.action ? answer(decision.action,'ascension') : wait(100,'ascension-blocked');
      }
      if(m.earlyFunding?.phase && m.earlyFunding.phase!=='complete'){const decision=runFunding();if(decision)return decision;}
      if (m.combo?.rebuy || m.combo?.confirmAura || m.combo?.auraRestore) {
        const decision=combine(o,actions,m.combo);m.combo=decision.memory;
        if(decision.action)return answer(decision.action,'combo-transaction');
        if(decision.exclusive)return wait(100,'combo-transaction-reserve');
      }
      // A controller can confirm only the prompt that it requested.
      if (m.confirmOneMind) {
        const pending=m.confirmOneMind;
        delete m.confirmOneMind;
        if (o.controls.promptOn && o.elapsedMs===pending.elapsedMs && o.upgrades['One mind']?.unlocked
          && !o.upgrades['One mind'].bought) return answer({type:'prompt',option:0},'research-confirmation');
      }
      if(m.confirmEarlyLevel) {
        const pending=m.confirmEarlyLevel;delete m.confirmEarlyLevel;
        if(o.controls.promptOn && o.elapsedMs===pending.elapsedMs && p.buildingLevels.Temple===pending.level)
          return answer({type:'prompt',option:0},'early-income-temple-confirmation');
      }
      if (o.controls.promptOn) {
        const owner = m.garden?.confirmSacrifice ? ['garden',tend]
          : m.season?.confirm ? ['season',collectSeason]
          : m.misc?.giftPending ? ['misc',collectMisc] : null;
        if (!owner) return wait(100,'unowned-prompt');
        const decision=owner[1](o,actions,m[owner[0]]); m[owner[0]]=decision.memory;
        return decision.action ? answer(decision.action,owner[0]) : wait(100,'unowned-prompt');
      }
      if (m.season?.helperPress || m.season?.helperReleaseAt != null) {
        const decision=collectSeason(o,actions,m.season); m.season=decision.memory;
        if (decision.action) return answer(decision.action,'season-pointer');
      }

      // Fixed presentation preferences reduce diagnostic work. They never depend
      // on a seed, a sampled outcome, or a search over future random events.
      if(lowEffects && !m.lowEffectsReady){
        const pref=['fancy','particles','numbers'].find(name=>o.controls.preferences[name]);
        if(pref)return answer({type:'preference',name:pref},'presentation-setup');
        if(o.controls.volume!==0)return answer({type:'volume',channel:'sound',value:0},'presentation-setup');
        m.lowEffectsReady=true;
      }
      if(lowEffects && o.achievements["Baby it's old outside"] && !m.helperEffectsRestored){
        if(o.controls.preferences.fancy)return answer({type:'preference',name:'fancy'},'presentation-setup');
        m.helperEffectsRestored=true;
      }

      if (!o.achievements["What's in a name"]) return answer({type:'name-bakery',name:'Completion Bakery'},'interface-achievements');
      if (!o.achievements['Tiny cookie']) return answer({type:'tiny-cookie'},'interface-achievements');
      if (!o.achievements['Here you go']) return answer({type:'achievement-slot',id:204},'interface-achievements');
      if (!o.achievements['Olden days']) return answer({type:'forgotten-madeleine'},'interface-achievements');
      if (!o.achievements['Tabloid addiction']) {
        if (!m.newsViewport) { m.newsViewport=true; return answer({type:'resize',width:1200,height:900},'interface-achievements'); }
        return answer({type:'click-news'},'interface-achievements');
      }
      if (!o.achievements['Stifling the press']) {
        if (!m.narrowViewport) { m.narrowViewport=true; return answer({type:'resize',width:800,height:900},'interface-achievements'); }
        return answer({type:'click-news'},'interface-achievements');
      }
      if (!m.restoreViewport) { m.restoreViewport=true; return answer({type:'resize',width:1200,height:900},'interface-achievements'); }
      if (o.controls.menu) return answer({type:'open-menu',menu:''},'interface-achievements');

      if(needHelperSetup) {
        const helperDecision=setupHelper(o,actions,m.helperSetup);m.helperSetup=helperDecision.memory;
        if(helperDecision.status==='blocked')throw new Error('Helper setup source boundary: '+helperDecision.reason);
        if(helperDecision.action)return answer(helperDecision.action,'two-art-helper-setup');
        if(helperDecision.status==='needs-resources') {
          const next=earlyGrow({...o,shop:{...o.shop,buildings:growthBuildings()}},actions,m.growth);m.growth=next.memory;
          return answer(next.action,'two-art-helper-funding');
        }
      }

      if(earlyCountPhase) {
        // Keep the early funding/count phase separate from unbounded collection.
        // Ripe nonmeaty harvests fund Temple1 without an unripe success trial.
        if(o.lump?.available && o.lump.ageMs>=o.lump.ripeAge && o.lump.ageMs<o.lump.overripeAge)
          return answer({type:'harvest-lump'},'early-income-lump');
        const temple=o.shop.buildings.find(b=>b.name==='Temple');
        if(temple?.amount>0 && temple.level===0 && o.lumps>=1) {
          m.confirmEarlyLevel={elapsedMs:o.elapsedMs,level:temple.level};
          return answer({type:'level-building',id:temple.id},'early-income-temple');
        }
        const decision=ascend(o,actions,m.ascension);m.ascension=decision.memory;
        if(decision.action && decision.action.type!=='wait')return answer(decision.action,'early-profitable-ascensions');
        if(temple?.amount>0 && p.minigames.Temple && o.controls.pantheon?.open===false)
          return answer({type:'minigame-open',id:temple.id},'early-income-pantheon');
        if(earlyFundingEnabled && temple?.amount>0 && p.minigames.Temple && o.elapsedMs>=(m.nextFundingAt||0)){
          const decision=runFunding();if(decision)return decision;
        }
        if(temple?.amount>0 && p.minigames.Temple) {
          const comboState={...(m.combo || {}),config:{...(m.combo?.config || {}),configureAuras:false,castHandOfFate:false,reserveCookies:0}};
          const decision=combine(o,actions,comboState);m.combo=decision.memory;
          if(decision.action)return answer(decision.action,'early-income-combo');
          if(decision.exclusive)return wait(100,'early-income-combo-reserve');
        }
        const needHardcore=preserveChallenges && !o.achievements.Hardcore;
        const needNeverclick=preserveChallenges && !o.achievements.Neverclick;
        const growthView={...o,decisionHorizonMs:1000,shop:{...o.shop,buildings:growthBuildings(),upgrades:needHardcore?[]:o.shop.upgrades.filter(u=>temple?.level>0 || u.name!=='One mind')}};
        const next=(needNeverclick?(o.cookieClicks>=15?earlyNoClick:growSingle):earlyGrow)(growthView,actions,m.growth);
        m.growth=next.memory;
        if(next.action.type==='buy-upgrade' && o.upgrades['One mind']?.id===next.action.id)
          m.confirmOneMind={elapsedMs:o.elapsedMs};
        return answer(next.action,needHardcore || needNeverclick?'challenge-achievements':'early-income-growth');
      }

      m.misc={...(m.misc || {}),deferGrandmaSaleUntilHardcore:preserveChallenges};
      const miscDecision=collectMisc(o,actions,m.misc); m.misc=miscDecision.memory;
      if (miscDecision.action) return answer(miscDecision.action,'misc');
      // Fading luck needs one cookie left on screen until its last second.
      // Only the owning controller can click that cookie during the hold.
      const held = new Set(miscDecision.deferShimmerIds || []);
      const publicObservation={...o,shimmers:o.shimmers.filter(s=>!held.has(s.id))};

      if (o.lump?.available && o.lump.ageMs >= (o.achievements['Hand-picked'] ? o.lump.ripeAge : o.lump.matureAge)
        && o.lump.ageMs < o.lump.overripeAge) return answer({type:'harvest-lump'},'sugar-resources');

      // A finite access schedule, not a claim about optimal lump allocation.
      const levels=[['Farm',1],['Farm',3],['Wizard tower',1],['Temple',1],['Bank',1],['Farm',9],['Cursor',12]];
      const target=levels.find(([name,level])=>p.buildingLevels[name]<level);
      if (target) {
        const b=o.shop.buildings.find(b=>b.name===target[0]);
        if (b?.amount>0 && o.lumps>=b.level+1) return answer({type:'level-building',id:b.id},'finite-unlocks');
      }
      // The last milk is unlocked at 600 normal achievements. The required
      // set plus the mandatory Cursor level gives only 599 in the worst case.
      const needsMilkLevel = !target && requiredNames.every(name=>o.achievements[name])
        && normalNames.filter(name=>o.achievements[name]).length<600 && p.buildingLevels.Farm===9;
      if (needsMilkLevel && o.lumps>=10) {
        return answer({type:'level-building',id:2},'milk-unlock');
      }

      const ascensionDecision=ascend(o,actions,m.ascension); m.ascension=ascensionDecision.memory;
      if (ascensionDecision.action && ascensionDecision.action.type!=='wait') return answer(ascensionDecision.action,'ascension');
      if(spellResetEnabled && ascensionDecision.status==='complete' && !m.finalCollectionStarted
        && !o.achievements['A wizard is you']) {
        const decision=runSpellReset();if(decision)return decision;
      }

      m.season={...(m.season || {}),config:{...(m.season?.config || {}),
        suppressWrathForCookieCount:naturalCookieFarm && ascensionDecision.status==='complete'}};
      const seasonDecision=collectSeason(publicObservation,actions,m.season); m.season=seasonDecision.memory;
      if (seasonDecision.action && seasonDecision.action.type!=='wait') return answer(seasonDecision.action,'season');
      if (seasonDecision.status==='needs-ascension' && !earlyCountPhase && m.ascension.config.allowReset
        && (!preserveChallenges || o.achievements.Hardcore && o.achievements.Neverclick)) {
        return answer({type:'ascend'},'season-retry');
      }
      const finalCollection=ascensionDecision.status==='complete' && seasonDecision.status==='complete'
        && (!spellResetEnabled || o.achievements['A wizard is you']);
      if(finalCollection)m.finalCollectionStarted=true;
      // The seasonal controller owns reindeer timing for Eldeer. Growth must
      // not immediately click a reindeer that this controller is holding.
      const growthShimmers=publicObservation.shimmers.filter(s=>s.type!=='reindeer');

      if (farmSugar && o.garden?.ready) {
        const finalLevels={Farm:9,'Wizard tower':1,Temple:1,Bank:1,Cursor:12};
        const levelCost=Object.entries(finalLevels).reduce((sum,[name,goal])=>{
          const now=Math.min(goal,p.buildingLevels[name]);
          return sum+(goal*(goal+1)-now*(now+1))/2;
        },needsMilkLevel ? 10 : 0);
        const harvests=Math.ceil(Math.max(0,levelCost-o.lumps)/10);
        m.garden={...(m.garden || {}),config:{...(m.garden?.config || {}),
          sacrificesRequired:Math.max(minimumSacrifices,o.garden.convertTimes+harvests)}};
      }
      m.garden={...(m.garden || {}),config:{...(m.garden?.config || {}),naturalCookieFarm:naturalCookieFarm && finalCollection}};
      const gardenDecision=tend(o,actions,m.garden);
      if (gardenDecision.action && gardenDecision.action.type!=='wait') {
        m.garden=gardenDecision.memory;
        return answer(gardenDecision.action,'garden');
      }
      m.garden=gardenDecision.memory;
      // Reserve an explicitly requested planting cost. Otherwise the growth
      // controller can spend every cookie and starve the Garden indefinitely.
      let reserve=Math.max(gardenDecision.status==='needs-resources' ? gardenDecision.requiredCookies || 0 : 0,
        miscDecision.status==='needs-resources' ? miscDecision.requiredCookies || 0 : 0,
        seasonDecision.status==='needs-resources' ? seasonDecision.requiredCookies || 0 : 0);
      const marketObservation={...o,cookies:Math.max(0,o.cookies-reserve)};
      m.market={...(m.market || {}),config:{...(m.market?.config || {}),
        collectTrades:collectTradesOverride ?? finalCollection}};
      const marketDecision=trade(marketObservation,actions,m.market);
      m.market=marketDecision.memory;
      if (marketDecision.status==='budget-exhausted') throw new Error('Stock Market controller decision budget exhausted');
      if (marketDecision.action && marketDecision.action.type!=='wait') {
        let action=marketDecision.action;
        if (reserve>0 && action.type==='market-buy' && action.amount===10000) {
          // Native 10000 means Max, not a numerical order size. Bound the
          // transaction using the unreserved bank before calling that API.
          const good=o.market.goods.find(g=>g.id===action.id);
          let amount=Math.min(9999,good.maxStock-good.stock,Math.floor(marketObservation.cookies/good.buyCookiePrice));
          while (amount>0 && good.buyCookiePrice*amount>marketObservation.cookies) amount--;
          if (amount<1) return wait(100,'market-reserve');
          action={...action,amount};
        }
        return answer(action,'market');
      }
      if (marketDecision.status==='needs-resources') reserve+=marketDecision.requiredCookies || 0;

      // Native office costs and seasonal sprite goals need particular buildings.
      // An income ranking alone need not ever choose those buildings.
      const request=[marketDecision,seasonDecision,gardenDecision].find(d=>d.building && d.amount>p.buildingAmounts[d.building]);
      if (request) {
        const b=o.shop.buildings.find(b=>b.name===request.building);
        if (b && !b.locked && b.buy1price<=o.cookies-reserve &&
          (request!==seasonDecision || o.elapsedMs>=(m.nextHelperBuilding || 0))) {
          if (request===seasonDecision) m.nextHelperBuilding=o.elapsedMs+34;
          return answer({type:'buy-building',id:b.id,amount:1},'required-building');
        }
        if (b && !b.locked) reserve=Math.max(reserve,b.buy1price);
      }

      m.production={...(m.production || {}),config:{...(m.production?.config || {}),finalCollection}};
      const productionDecision=produce({...o,cookies:Math.max(0,o.cookies-reserve)},actions,m.production);
      m.production=productionDecision.memory;
      if (productionDecision.action && productionDecision.action.type!=='wait') return answer(productionDecision.action,'production');
      if (productionDecision.status==='needs-resources') reserve=Math.max(reserve,productionDecision.requiredCookies || 0);

      // Continue the same real income controller through later prestige growth.
      // Final current building holdings are collected after this phase ends.
      if(earlyFundingEnabled && !m.finalCollectionStarted && ascensionDecision.status!=='complete'
        && o.elapsedMs>=(m.nextFundingAt||0)){
        const decision=runFunding(reserve);if(decision)return decision;
      }

      m.combo={...(m.combo || {}),config:{...(m.combo?.config || {}),reserveCookies:reserve,deferredShimmerIds:[...held]}};
      const comboDecision=combine(o,actions,m.combo);m.combo=comboDecision.memory;
      if(comboDecision.action)return answer(comboDecision.action,'combo');
      if(comboDecision.exclusive)return wait(100,'combo-transaction-reserve');

      // These goals use native callbacks and never inspect a spell's outcome.
      if (o.santa?.canUpgrade && o.cookies-o.santa.price>=reserve) return answer({type:'upgrade-santa'},'santa');
      if (o.dragon?.nextCanUpgrade && reserve===0) return answer({type:'upgrade-dragon'},'dragon');
      const grimoire=o.controls.grimoire;
      if (p.minigames['Wizard tower'] && grimoire && !o.achievements['A wizard is you']) {
        // These spells always finish their callback. A cheaper unavailable
        // spell can refund its cost and leave the policy in a zero-time loop.
        const safeSpells=['conjure baked goods','hand of fate',"haggler's charm",'summon crafty pixies','diminish ineptitude'];
        const spell=Object.entries(grimoire.spells).filter(([key,s])=>safeSpells.includes(key) && s.cost<=grimoire.magic-(comboDecision.reserveMagic || 0)
          && !(reserve>0 && key==='conjure baked goods'))
          .sort((a,b)=>a[1].cost-b[1].cost || a[0].localeCompare(b[0]))[0];
        if (spell) return answer({type:'cast-spell',spell:spell[0]},'spell-count');
      }
      const needHardcore=preserveChallenges && !o.achievements.Hardcore;
      const needNeverclick=preserveChallenges && !o.achievements.Neverclick;
      const decisionHorizonMs=Math.min(miscDecision.wakeAfterMs || 1000,
        gardenDecision.action?.type==='wait' ? gardenDecision.action.milliseconds : 1000,
        marketDecision.action?.type==='wait' ? marketDecision.action.milliseconds : 1000,
        seasonDecision.action?.type==='wait' ? seasonDecision.action.milliseconds : 1000,
        productionDecision.action?.type==='wait' ? productionDecision.action.milliseconds : 1000);
      const growObservation={...o,decisionHorizonMs,shimmers:growthShimmers,cookies:Math.max(0,o.cookies-reserve),shop:{...o.shop,
        buildings:growthBuildings(),upgrades:needHardcore ? [] : o.shop.upgrades}};
      const next=(needNeverclick ? (o.cookieClicks>=15 ? growWithoutClicks : growSingle) : grow)(growObservation,actions,m.growth);
      m.growth=next.memory;
      if (next.action.type==='wait' && gardenDecision.action?.type==='wait') {
        next.action={...next.action,milliseconds:Math.min(next.action.milliseconds,gardenDecision.action.milliseconds)};
      }
      if (next.action.type==='wait' && marketDecision.action?.type==='wait') {
        next.action={...next.action,milliseconds:Math.min(next.action.milliseconds,marketDecision.action.milliseconds)};
      }
      if (next.action.type==='wait') next.action={...next.action,milliseconds:Math.min(next.action.milliseconds,
        miscDecision.wakeAfterMs || 1000,seasonDecision.action?.type==='wait' ? seasonDecision.action.milliseconds : 1000,
        productionDecision.action?.type==='wait' ? productionDecision.action.milliseconds : 1000)};
      if (next.action.type==='buy-upgrade' && o.upgrades['One mind']?.id===next.action.id) {
        m.confirmOneMind={elapsedMs:o.elapsedMs};
      }
      return answer(next.action,needHardcore || needNeverclick ? 'challenge-achievements' : 'growth');
    };
  })()

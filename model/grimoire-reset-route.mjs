import assert from "node:assert/strict";
import { readFileSync } from "node:fs";
import { createHash } from "node:crypto";
import { createRuntime } from "./runtime.mjs";
import { SOURCE_HASHES } from "./game-source.mjs";
export function probeFundedGrimoireResetRoute({
  sourceDirectory,
  count = 999,
  randomSeed = 1,
} = {}) {
  assert(Number.isSafeInteger(count) && count > 0 && count <= 999);
  const r = createRuntime({ sourceDirectory, randomSeed, recordAudit: false });
  const G = r.Game;
  const act = (a) => r.act(a, { observe: false });
  const wait = (milliseconds) => act({ type: "wait", milliseconds });
  // One explicit prerequisite boundary; no resources are injected after setup.
  G.cookies = G.cookiesEarned = 1e57;
  G.lumps = G.lumpsTotal = 1;
  wait(200);
  act({ type: "buy-building", id: 7, amount: 1 });
  act({ type: "level-building", id: 7 });
  if (G.promptOn) act({ type: "prompt", option: 0 });
  wait(20);
  const enterHeaven = () => {
    act({ type: "ascend" });
    act({ type: "key", code: 27, down: true });
    act({ type: "key", code: 27, down: false });
    wait(40);
    assert(G.OnAscend);
  };
  enterHeaven();
  const bought = [];
  function buyWithParents(u) {
    if (u.bought) return;
    for (const p of u.parents || []) if (p !== -1) buyWithParents(p);
    act({ type: "buy-upgrade", id: u.id });
    assert(u.bought);
    bought.push(u.name);
  }
  buyWithParents(G.Upgrades.Legacy);
  buyWithParents(G.Upgrades["Starter kitchen"]);
  const entry = {
    prestige: G.prestige,
    heavenlyChips: G.heavenlyChips,
    bought,
    priorCookiesReset: G.cookiesReset,
    earnedBeingForfeited: G.cookiesEarned,
    lumps: G.lumps,
  };
  act({ type: "reincarnate", mode: 0 });
  const M = G.Objects["Wizard tower"].minigame;
  const start = r.clock.now;
  const rows = [];
  const outcomes = { success: 0, backfire: 0 };
  for (let i = 0; i < count; i++) {
    wait(5100);
    assert.equal(G.ReincarnateTimer, 0);
    assert.equal(G.OnAscend, 0);
    assert(G.Upgrades["Heavenly chip secret"].unlocked);
    assert(G.cookies >= 11);
    const beforeSecret = { cookies: G.cookies, cps: G.cookiesPs };
    act({ type: "buy-upgrade", id: G.Upgrades["Heavenly chip secret"].id });
    wait(200);
    const beforeTower = {
      cookies: G.cookies,
      cps: G.cookiesPs,
      price: G.Objects["Wizard tower"].getSumPrice(1),
    };
    act({ type: "buy-building", id: 7, amount: 1 });
    if (!G.Objects["Wizard tower"].onMinigame)
      act({ type: "minigame-open", id: 7 });
    assert.equal(M.magicM, 5);
    assert.equal(M.magic, 5);
    assert.equal(M.getSpellCost(M.spells["conjure baked goods"]), 4);
    const beforeCast = {
      cookies: G.cookies,
      earned: G.cookiesEarned,
      count: M.spellsCastTotal,
    };
    act({ type: "cast-spell", spell: "conjure baked goods" });
    assert.equal(M.spellsCastTotal, beforeCast.count + 1);
    assert.equal(M.magic, 1);
    const failure = !!G.hasBuff("Clot");
    outcomes[failure ? "backfire" : "success"]++;
    const afterCast = {
      cookies: G.cookies,
      earned: G.cookiesEarned,
      count: M.spellsCastTotal,
      failed: failure,
    };
    enterHeaven();
    act({ type: "reincarnate", mode: 0 });
    assert.equal(M.magic, 5);
    assert.equal(M.spellsCastTotal, i + 1);
    assert.equal(G.Objects["Wizard tower"].amount, 0);
    assert(!G.hasBuff("Clot"));
    assert.equal(G.lumps, 0);
    assert.equal(G.Objects["Wizard tower"].level, 1);
    if (i < 3 || i === count - 1)
      rows.push({
        cycle: i + 1,
        beforeSecret,
        beforeTower,
        beforeCast,
        afterCast,
        elapsed: r.clock.now - start,
      });
  }
  wait(1100);
  assert.equal(G.OnAscend, 0);
  assert.equal(G.ReincarnateTimer, 0);
  assert.equal(M.spellsCastTotal, count);
  if (count === 999) assert(G.HasAchiev("A wizard is you"));
  const result = {
    sourceHashes: SOURCE_HASHES,
    runtimeSha256: createHash("sha256")
      .update(readFileSync(new URL("./runtime.mjs", import.meta.url)))
      .digest("hex"),
    host: process.versions,
    scope:
      "Actual native source in diagnostic DOM/clock adapter, from an explicit initial1e57-cookie/one-lump prerequisite. No later funding, level, mana, achievement or outcome mutation. No claim of legal new-save reachability, physical input refinement or global optimum.",
    entry,
    cycles: count,
    outcomes,
    elapsedMilliseconds: r.clock.now - start,
    resetCount: G.resets,
    spells: M.spellsCastTotal,
    lumps: G.lumps,
    level: G.Objects["Wizard tower"].level,
    achievement: !!G.HasAchiev("A wizard is you"),
    normalMode:
      G.ascensionMode === 0 &&
      !G.OnAscend &&
      !G.AscendTimer &&
      !G.ReincarnateTimer,
    rows,
  };
  return result;
}

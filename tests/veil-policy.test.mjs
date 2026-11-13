import test from "node:test";
import assert from "node:assert/strict";
import { createRuntime } from "../model/runtime.mjs";
import { hasGameSource } from "../model/game-source.mjs";
import { decidePolicy } from "../model/policy-runtime.mjs";
import { completionPolicySource } from "../model/completion-policy.mjs";
import { decideFinalRun } from "../model/final-run-policy.mjs";
import { veilPolicySource } from "../model/veil-policy.mjs";
const skip = !hasGameSource() && "Pinned Steam source unavailable";
const past = [
  "Hardcore",
  "Neverclick",
  "Rebirth",
  "Resurrection",
  "Reincarnation",
  "All the stars in heaven",
  "No more room in hell",
  "Debt evasion",
  "And a little extra",
  "Speed's the name of the game (no it's not it's called Cookie Clicker)",
  "What's not clicking",
  "What's in a name",
  "Tiny cookie",
  "Here you go",
  "Olden days",
  "Tabloid addiction",
  "Stifling the press",
  "Cookie-dunker",
  "Just wrong",
  "Early bird",
  "Fading luck",
  "No time like the present",
];
const quiet = {
  helperSetup: false,
  season: {
    seasons: [],
    research: false,
    fortunes: false,
    dragonDrops: false,
    wrinklers: false,
    helperGrandma: false,
    eldeer: false,
    reindeerTarget: 0,
  },
};
function entry({
  wizard = false,
  veil = false,
  maintenanceReload = null,
} = {}) {
  const r = createRuntime({
      recordAudit: false,
      randomSeed: 1,
      maintenanceReload,
    }),
    G = r.Game;
  // Supplied past milestones/history and current funding isolate the composed
  // source phase. No assignments are made after this entry, including seeds.
  G.cookies = G.cookiesEarned = 1e57;
  G.cookiesReset = 1e57;
  G.prestige = 1e15;
  G.resets = 100;
  G.lumps = G.lumpsTotal = 1;
  for (const name of past) G.Win(name);
  if (wizard) G.Win("A wizard is you");
  if (veil) G.Win("Thick-skinned");
  for (const u of Object.values(G.Upgrades))
    if (u.pool === "prestige") {
      u.bought = 1;
      u.unlocked = 1;
    }
  r.advance(200);
  r.act({ type: "buy-building", id: 7, amount: 1 });
  r.act({ type: "level-building", id: 7 });
  if (G.promptOn) r.act({ type: "prompt", option: 0 });
  r.advance(20);
  G.Objects["Wizard tower"].minigame.spellsCastTotal = wizard ? 999 : 998;
  return r;
}
function run(r) {
  const source = completionPolicySource(quiet);
  let memory = { restoreViewport: true };
  const records = [];
  for (let i = 0; i < 700; i++) {
    const before = r.snapshot();
    let d;
    try {
      d = decidePolicy(source, before, [], memory);
    } catch (error) {
      console.error(
        JSON.stringify({
          stage: "diagnostic-error",
          elapsedMs: before.elapsedMs,
          progression: before.progression,
          controls: {
            promptOn: before.controls.promptOn,
            menu: before.controls.menu,
          },
          memory,
          actions: records.slice(-8),
        }),
      );
      throw error;
    }
    memory = d.memory;
    if (memory.finalPreparationComplete)
      return { memory, records, after: r.snapshot() };
    records.push({
      stage: d.stage,
      action: d.action,
      counter: before.cookieClicks,
    });
    if (d.stage === "direct-veil" && d.action.type === "click")
      assert.equal(before.cookiesPs, 0);
    for (const a of d.action.type === "sequence"
      ? d.action.actions
      : [d.action])
      r.act(a);
  }
  assert.fail("conditional phase did not finish within the diagnostic budget");
}
test(
  "actual composed spell release reuses its final reincarnation and completes direct free veil trials",
  { skip },
  () => {
    const r = entry(),
      result = run(r);
    assert(result.after.achievements["A wizard is you"]);
    assert(result.after.achievements["Thick-skinned"]);
    assert.equal(result.memory.finalRun.reusedSpellBoundary, true);
    assert.equal(
      result.records.filter((x) => x.action.type === "ascend").length,
      2,
    );
    assert(
      result.records.some(
        (x) =>
          x.stage === "spell-count-resets" && x.action.type === "cast-spell",
      ),
    );
    const clicks = result.records.filter(
      (x) => x.stage === "direct-veil" && x.action.type === "click",
    );
    assert(clicks.length >= 1 && clicks.length <= 35);
    assert.deepEqual(
      clicks.map((x) => x.counter),
      Array.from({ length: clicks.length }, (_, i) => i),
    );
    assert(result.after.shop.buildings.every((b) => b.amount === 0));
    assert.equal(result.after.cookiesPs, 0);
    const lastCast = result.records.findLastIndex(
      (x) => x.action.type === "cast-spell",
    );
    assert.equal(
      result.records
        .slice(lastCast + 1)
        .filter((x) => x.action.type === "ascend").length,
      1,
      "only the fixed final spell reset follows the cast",
    );
  },
);
test(
  "precommitted final reset schedule is independent of already-won veil and wizard flags",
  { skip },
  () => {
    for (const wizard of [false, true]) {
      const failed = run(entry({ wizard, veil: false })),
        won = run(entry({ wizard, veil: true }));
      const resetActions = (result) =>
        result.records
          .filter((x) => ["ascend", "reincarnate"].includes(x.action.type))
          .map((x) => x.action);
      assert.deepEqual(resetActions(failed), resetActions(won));
      assert.equal(failed.memory.finalRun.reusedSpellBoundary, !wizard);
      assert.equal(won.memory.finalRun.reusedSpellBoundary, !wizard);
      assert.equal(
        resetActions(failed).filter((a) => a.type === "ascend").length,
        wizard ? 1 : 2,
      );
    }
  },
);
test(
  "the final preparation rule itself never reads either random-goal flag or a seed",
  { skip },
  () => {
    const o = entry({ wizard: true }).snapshot(),
      options = { released: true, allowReset: true };
    const original = decideFinalRun(o, {}, options);
    const altered = {
      ...o,
      seed: "not an input capability",
      achievements: {
        ...o.achievements,
        "Thick-skinned": true,
        "A wizard is you": false,
      },
    };
    assert.deepEqual(decideFinalRun(altered, {}, options), original);
    assert.deepEqual(original.action, { type: "ascend" });
    assert.equal(
      decideFinalRun(o, {}, { ...options, allowReset: false }).status,
      "deferred",
    );
  },
);
test(
  "a fixed maintenance reload during the final phase retains the current state and source prefix",
  { skip },
  () => {
    const r = entry({
        wizard: true,
        maintenanceReload: { firstMs: 4000, everyMs: 20000 },
      }),
      result = run(r);
    assert(result.after.achievements["Thick-skinned"]);
    assert(r.auditCounts().reloadCount >= 1);
    assert.equal(
      result.records.filter((x) => x.action.type === "ascend").length,
      1,
    );
  },
);
test(
  "flat egg production is an explicit boundary rather than a free-veil assumption",
  { skip },
  () => {
    const r = entry({ wizard: true });
    r.Game.Objects["Wizard tower"].amount = 0;
    r.Game.BuildingsOwned = 0;
    r.Game.Upgrades['"egg"'].bought = 1;
    r.Game.CalculateGains();
    const d = decidePolicy(
      veilPolicySource({ released: true }),
      r.snapshot(),
      [],
      { active: true, phase: "ready", nextCounter: 0 },
    );
    assert.equal(d.status, "blocked");
    assert.match(d.reason, /production/);
  },
);

test(
  "final-run preparation excludes only the flat-production egg from permanent assignment",
  { skip },
  () => {
    const r = entry({ wizard: true }),
      o = r.snapshot();
    // Public-offer arbitration fixture, not a native earned ownership trace.
    o.progression.onAscend = true;
    o.progression.ascendTimer = 0;
    o.progression.reincarnateTimer = 0;
    o.ascension.permanentSlots = [-1, -1, -1, -1, -1];
    o.ascension.permanentCandidates = [
      { id: r.Game.Upgrades['"egg"'].id, name: '"egg"', price: 1e100 },
    ];
    const d = decidePolicy(completionPolicySource(quiet), o, [], {
      restoreViewport: true,
    });
    assert.notEqual(d.action.type, "permanent-slot");
    assert.deepEqual(d.action, { type: "reincarnate", mode: 0 });
    const legacy = decidePolicy(
      completionPolicySource({ ...quiet, finalPreparation: false }),
      o,
      [],
      { restoreViewport: true },
    );
    assert.equal(legacy.action.type, "permanent-slot");
    assert.equal(legacy.action.id, r.Game.Upgrades['"egg"'].id);
  },
);

test(
  "a maintenance request due during ascent preserves final preparation through the deferred native prompt",
  { skip },
  () => {
    const r = entry({
        wizard: true,
        maintenanceReload: { firstMs: 250, everyMs: 20000 },
      }),
      result = run(r);
    assert(result.after.achievements["Thick-skinned"]);
    assert(r.auditCounts().reloadCount >= 1);
    assert(
      result.records.filter((x) => x.action.type === "ascend").length >= 1,
    );
  },
);

test(
  "exclusive spell phase waits through a deferred native maintenance prompt without losing its cast quota",
  { skip },
  () => {
    const r = entry({
        wizard: false,
        maintenanceReload: { firstMs: 5350, everyMs: 20000 },
      }),
      result = run(r);
    assert(result.after.achievements["A wizard is you"]);
    assert(result.after.achievements["Thick-skinned"]);
    assert(r.auditCounts().reloadCount >= 1);
    assert.equal(result.after.controls.grimoire.spellsCastTotal, 999);
    assert.equal(
      result.records.filter((x) => x.action.type === "cast-spell").length,
      1,
    );
    assert.equal(result.memory.finalRun.reusedSpellBoundary, true);
  },
);

import test from "node:test";
import assert from "node:assert/strict";
import { createRuntime } from "../model/runtime.mjs";
import { hasGameSource } from "../model/game-source.mjs";
import {
  decideGrimoireResetAction,
  grimoireResetPolicySource,
} from "../model/grimoire-reset-policy.mjs";
import { completionPolicySource } from "../model/completion-policy.mjs";
import { decidePolicy } from "../model/policy-runtime.mjs";
const skip = !hasGameSource() && "Pinned game source unavailable";
const entryGoals = [
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
const options = {
  allowReset: true,
  ascensionReady: true,
  collectionStarted: false,
};
function observation() {
  return {
    elapsedMs: 0,
    ascensions: 100,
    prestige: 1e15,
    achievements: Object.fromEntries(entryGoals.map((n) => [n, true])),
    upgrades: Object.fromEntries(
      ["Legacy", "Starter kit", "Starter kitchen"].map((n) => [
        n,
        { bought: true },
      ]),
    ),
    controls: {
      promptOn: false,
      menu: "",
      grimoire: { spellsCastTotal: 995, magic: 5, magicMax: 5, open: false },
    },
    progression: {
      ascensionMode: 0,
      onAscend: false,
      ascendTimer: 0,
      reincarnateTimer: 0,
      buildingLevels: { "Wizard tower": 1 },
      buildingAmounts: { "Wizard tower": 0 },
      minigames: { "Wizard tower": true },
    },
  };
}

test("spell resets require completed profitable ascensions, growth release and pre-collection entry", () => {
  const changes = [
    (o) => (o.ascensions = 99),
    (o) => (o.prestige = 2 ** 49 - 1),
    (o) => (o.prestige = Infinity),
    (o) => (o.controls.promptOn = true),
    (o) => (o.controls.menu = "stats"),
    (o) => (o.progression.ascensionMode = 1),
    (o) => (o.progression.buildingLevels["Wizard tower"] = 2),
    (o) => (o.progression.minigames["Wizard tower"] = false),
    (o) => (o.progression.onAscend = true),
    (o) => (o.progression.reincarnateTimer = 1),
    (o) => (o.achievements.Reincarnation = false),
    (o) => (o.achievements["And a little extra"] = false),
    (o) => (o.upgrades["Starter kitchen"].bought = false),
    (o) => (o.controls.grimoire.spellsCastTotal = 999),
  ];
  for (const change of changes) {
    const o = observation();
    change(o);
    const d = decideGrimoireResetAction(o, {}, options);
    assert.equal(d.status, "deferred");
    assert.equal(d.action, null);
  }
  for (const config of [
    { allowReset: false },
    { ascensionReady: false },
    { collectionStarted: true },
  ]) {
    assert.equal(
      decideGrimoireResetAction(observation(), {}, { ...options, ...config })
        .status,
      "deferred",
    );
  }
});
test("the fixed quota retains earlier casts and skips a completed native achievement", () => {
  const o = observation();
  const before = structuredClone(o);
  const d = decideGrimoireResetAction(o, {}, options);
  assert.equal(d.memory.targetCasts, 4);
  assert.equal(d.memory.startCount, 995);
  assert.deepEqual(d.action, { type: "ascend" });
  assert.deepEqual(o, before);
  o.achievements["A wizard is you"] = true;
  const complete = decideGrimoireResetAction(o, {}, options);
  assert.equal(complete.status, "complete");
  assert.equal(complete.action, null);
});
test("the phase refuses a stalled native cast and a stale magic capacity", () => {
  const o = observation();
  const m = {
    active: true,
    phase: "count",
    startCount: 995,
    completedCasts: 0,
    targetCasts: 4,
  };
  assert.equal(decideGrimoireResetAction(o, m, options).status, "blocked");
  o.progression.buildingAmounts["Wizard tower"] = 1;
  o.controls.grimoire.magicMax = 112;
  m.phase = "cast";
  assert.equal(decideGrimoireResetAction(o, m, options).status, "blocked");
});
test("an active spell phase has priority over other completion controllers and animations", () => {
  const o = observation();
  const memory = {
    spellReset: {
      active: true,
      phase: "ascend",
      startCount: 995,
      completedCasts: 0,
      targetCasts: 4,
    },
  };
  const d = decidePolicy(completionPolicySource(), o, [], memory);
  assert.equal(d.stage, "spell-count-resets");
  assert.deepEqual(d.action, { type: "ascend" });
  o.progression.ascendTimer = 1;
  const transition = decidePolicy(completionPolicySource(), o, [], d.memory);
  assert.equal(transition.stage, "spell-count-resets");
  assert.equal(transition.action.type, "sequence");
});

function suppliedEntry(startCount = 998, failure = false) {
  const r = createRuntime({ recordAudit: false }),
    G = r.Game;
  // Supplied late-game history and funding, not a trace from a new save.
  // No resource, counter or achievement assignments occur after this setup.
  G.cookies = G.cookiesEarned = 1e57;
  G.lumps = G.lumpsTotal = 1;
  G.resets = 100;
  for (const name of entryGoals) G.Win(name);
  const act = (a) =>
    a.type === "sequence"
      ? a.actions.forEach(act)
      : r.act(a, { observe: false });
  act({ type: "wait", milliseconds: 200 });
  act({ type: "buy-building", id: 7, amount: 1 });
  act({ type: "level-building", id: 7 });
  if (G.promptOn) act({ type: "prompt", option: 0 });
  act({ type: "wait", milliseconds: 20 });
  const M = G.Objects["Wizard tower"].minigame;
  M.spellsCastTotal = startCount;
  act({ type: "ascend" });
  act({ type: "key", code: 27, down: true });
  act({ type: "key", code: 27, down: false });
  act({ type: "wait", milliseconds: 40 });
  function buy(u) {
    if (u.bought) return;
    for (const p of u.parents || []) if (p !== -1) buy(p);
    act({ type: "buy-upgrade", id: u.id });
  }
  buy(G.Upgrades.Legacy);
  buy(G.Upgrades["Starter kitchen"]);
  act({ type: "reincarnate", mode: 0 });
  act({ type: "wait", milliseconds: 1100 });
  const cast = M.castSpell;
  // Source test option selects each intact branch; the policy receives no
  // branch control and production actions use the ordinary one-argument API.
  M.castSpell = (spell) => cast(spell, { failChanceSet: failure ? 1 : 0 });
  return { r, G, M, act };
}
function runPhase(fixture) {
  const { r, G, M, act } = fixture;
  const initial = {
    resets: G.resets,
    lumps: G.lumps,
    count: M.spellsCastTotal,
  };
  const source = grimoireResetPolicySource(options);
  let memory = {};
  const actions = [];
  for (let n = 0; n < 100; n++) {
    const d = decidePolicy(source, r.snapshot(), [], memory);
    memory = d.memory;
    assert.notEqual(d.status, "blocked", d.reason);
    assert.notEqual(d.status, "deferred", d.reason);
    if (d.status === "complete")
      return {
        actions,
        memory,
        initial,
        after: {
          resets: G.resets,
          lumps: G.lumps,
          count: M.spellsCastTotal,
          achievement: !!G.HasAchiev("A wizard is you"),
          clot: !!G.hasBuff("Clot"),
          normal: !G.OnAscend && !G.AscendTimer && !G.ReincarnateTimer,
        },
      };
    assert(d.action);
    actions.push(d.action);
    act(d.action);
  }
  throw new Error(
    "The finite phase did not finish its diagnostic action budget",
  );
}
test(
  "both native Conjure outcomes use the same schedule and zero-profit resets do not satisfy Reincarnation",
  { skip },
  () => {
    const success = runPhase(suppliedEntry(998, false)),
      failure = runPhase(suppliedEntry(998, true));
    assert.deepEqual(success.actions, failure.actions);
    for (const result of [success, failure]) {
      assert.equal(result.memory.targetCasts, 1);
      assert.equal(result.memory.completedCasts, 1);
      assert.equal(result.after.count, 999);
      assert.equal(result.after.achievement, true);
      assert.equal(result.after.normal, true);
      assert.equal(result.after.clot, false);
      assert.equal(result.after.lumps, result.initial.lumps);
      assert.equal(result.after.resets, result.initial.resets);
    }
  },
);
test(
  "a partially earned native quota completes its remaining four casts without a resource refill",
  { skip },
  () => {
    const result = runPhase(suppliedEntry(995, true));
    assert.equal(result.memory.targetCasts, 4);
    assert.equal(result.memory.completedCasts, 4);
    assert.equal(
      result.actions.filter((a) => a.type === "cast-spell").length,
      4,
    );
    assert.equal(result.after.count, 999);
    assert.equal(result.after.resets, result.initial.resets);
  },
);

test(
  "one cast before a funded profitable reset preserves its earned-cookie milestone on either outcome",
  { skip },
  () => {
    for (const failure of [false, true]) {
      const r = createRuntime({ recordAudit: false }),
        G = r.Game;
      // One supplied early-growth boundary, independent of the later reset route.
      G.cookies = G.cookiesEarned = 2 ** 90;
      G.lumps = G.lumpsTotal = 1;
      r.advance(200);
      r.act({ type: "buy-building", id: 7, amount: 1 });
      r.act({ type: "level-building", id: 7 });
      if (G.promptOn) r.act({ type: "prompt", option: 0 });
      r.advance(20);
      const M = G.Objects["Wizard tower"].minigame,
        before = G.cookiesEarned;
      assert(
        M.castSpell(M.spells["conjure baked goods"], {
          failChanceSet: failure ? 1 : 0,
        }),
      );
      assert(G.cookiesEarned >= before);
      assert.equal(M.spellsCastTotal, 1);
      r.act({ type: "ascend" });
      r.act({ type: "key", code: 27, down: true });
      r.act({ type: "key", code: 27, down: false });
      r.advance(40);
      assert(G.gainedPrestige > 0);
      r.act({ type: "reincarnate", mode: 0 });
      assert.equal(G.resets, 1);
      assert.equal(M.spellsCastTotal, 1);
      assert.equal(M.magic, 5);
    }
  },
);

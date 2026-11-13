/** A fixed spell-count schedule; this is not a full-game optimum certificate. */
function resetDecision(o, memory, options) {
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
  if (o.controls?.promptOn || o.controls?.menu)
    return wait(1000, "Allow the native scheduled maintenance prompt and restoration to finish.");
  if (!P || P.ascensionMode !== 0 || !M) {
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
}

export function decideGrimoireResetAction(
  observation,
  memory = {},
  options = {},
) {
  return resetDecision(observation, memory, options);
}

export function grimoireResetPolicySource(options = {}) {
  return `(function (observation, actions, memory) {
    return (${resetDecision.toString()})(observation, memory, {...${JSON.stringify(options)}, ...((memory || {}).config || {})});
  })`;
}

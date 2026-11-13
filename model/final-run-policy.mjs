/** One precommitted final-run boundary, independent of veil outcomes or seeds. */
function finalRunDecision(o, memory, options) {
  const config = {
    released: false,
    allowReset: false,
    boundarySupplied: false,
    ...options,
    ...(memory?.config || {}),
  };
  const m = { ...(memory || {}) };
  const answer = (status, reason, action = null) => ({
    status,
    reason,
    action,
    memory: m,
  });
  const act = (reason, action) => answer("acting", reason, action);
  const wait = (ms, reason) => act(reason, { type: "wait", milliseconds: ms });
  const P = o.progression;
  if (m.phase === "complete")
    return answer(
      "complete",
      "The one planned final normal-run boundary is ready.",
    );
  if (!m.active) {
    if (
      !config.released ||
      !config.allowReset ||
      !P ||
      P.ascensionMode !== 0 ||
      P.onAscend ||
      P.ascendTimer ||
      P.reincarnateTimer ||
      o.controls?.promptOn ||
      o.controls?.menu
    )
      return answer(
        "deferred",
        "The scheduler has not released final-run preparation.",
      );
    m.active = true;
    if (config.boundarySupplied) {
      if (o.cookieClicks !== 0)
        return answer(
          "blocked",
          "The supplied final reincarnation already contains a cookie click.",
        );
      m.reusedSpellBoundary = true;
      m.phase = "verify";
      return wait(5100, "Allow the native final-run activation checks.");
    }
    m.phase = "transition";
    m.reusedSpellBoundary = false;
    return act("Begin the one final-collection preparation reset.", {
      type: "ascend",
    });
  }
  if (!config.allowReset || !P || P.ascensionMode !== 0)
    return answer(
      "blocked",
      "The owned final-run preparation was interrupted.",
    );
  if (o.controls?.promptOn || o.controls?.menu)
    return wait(
      1000,
      "Allow the native scheduled maintenance prompt and restoration to finish.",
    );
  if (P.ascendTimer > 0) {
    if (!m.escapeSent) {
      m.escapeSent = true;
      return act("Finish the planned ascension animation.", {
        type: "sequence",
        actions: [
          { type: "key", code: 27, down: true },
          { type: "key", code: 27, down: false },
        ],
      });
    }
    return wait(40, "Allow the next native ascension frame.");
  }
  delete m.escapeSent;
  if (P.onAscend) {
    if (P.reincarnateTimer)
      return wait(100, "Finish the planned reincarnation.");
    m.phase = "activation";
    return act("Enter the fixed final normal run.", {
      type: "reincarnate",
      mode: 0,
    });
  }
  if (P.reincarnateTimer) return wait(100, "Finish the normal-run animation.");
  if (m.phase === "activation") {
    m.phase = "verify";
    return wait(5100, "Allow the native final-run activation checks.");
  }
  if (m.phase === "verify") {
    if (o.cookieClicks !== 0)
      return answer(
        "blocked",
        "A cookie click interrupted final-run preparation.",
      );
    m.active = false;
    m.phase = "complete";
    return answer(
      "complete",
      "The one planned final normal-run boundary is ready.",
    );
  }
  return answer(
    "blocked",
    "The planned final reset did not enter its next source phase.",
  );
}
export function finalRunPolicySource(options = {}) {
  return `(function(o,actions,memory){return (${finalRunDecision.toString()})(o,memory,${JSON.stringify(options)});})`;
}
export function decideFinalRun(o, m = {}, options = {}) {
  return finalRunDecision(o, m, options);
}

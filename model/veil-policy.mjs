/** Direct native veil trials after an independently planned final normal run.
 * The all-seed 35-click cover is exhaustive native evidence, not a Lean theorem. */
function veilDecision(o, memory, options) {
  const config = { released: false, ...options, ...(memory?.config || {}) };
  const m = { ...(memory || {}) };
  const answer = (status, reason, action = null) => ({
    status,
    reason,
    action,
    memory: m,
  });
  const act = (reason, action) => answer("acting", reason, action);
  const wait = (reason) => act(reason, { type: "wait", milliseconds: 34 });
  if (o.achievements?.["Thick-skinned"]) {
    m.active = false;
    m.phase = "complete";
    return answer("complete", "The native veil achievement is won.");
  }
  const P = o.progression;
  if (!m.active) {
    if (
      !config.released ||
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
        "The scheduler has not supplied the final normal-run boundary.",
      );
    if (
      o.cookieClicks !== 0 ||
      ![
        "Shimmering veil",
        "Reinforced membrane",
        "Delicate touch",
        "Steadfast murmur",
        "Glittering edge",
      ].every((name) => o.upgrades?.[name]?.bought)
    )
      return answer(
        "blocked",
        "Use the untouched first-click boundary with all four veil defense upgrades.",
      );
    m.active = true;
    m.phase = "sell";
    m.nextCounter = 0;
  }
  if (
    !P ||
    P.ascensionMode !== 0 ||
    P.onAscend ||
    P.ascendTimer ||
    P.reincarnateTimer
  )
    return answer("blocked", "The owned direct veil phase was interrupted.");
  if (o.controls?.promptOn || o.controls?.menu)
    return act(
      "Allow the native scheduled maintenance prompt and restoration to finish.",
      { type: "wait", milliseconds: 1000 },
    );
  if (m.phase === "sell") {
    const building = o.shop.buildings.find((b) => b.amount > 0);
    if (building)
      return act(
        "Sell the remaining starter buildings before the direct veil trials.",
        {
          type: "sell-building",
          id: building.id,
          amount: Math.min(1000, building.amount),
        },
      );
    m.phase = "ready";
    return wait("Allow the native zero-building gains update.");
  }
  if (m.phase === "clicked") {
    if (o.cookieClicks !== m.nextCounter + 1)
      return answer(
        "blocked",
        "The native first-click sequence was not accepted exactly once.",
      );
    m.nextCounter += 1;
    m.phase = "ready";
  }
  if (
    m.phase !== "ready" ||
    o.cookieClicks !== m.nextCounter ||
    m.nextCounter >= 35
  )
    return answer(
      "blocked",
      "The observed counter left the checked 35-click prefix.",
    );
  if (o.shop.buildings.some((b) => b.amount !== 0) || o.cookiesPs !== 0)
    return answer(
      "blocked",
      "A nonzero production effect prevents the zero-building veil profile.",
    );
  if (!o.upgrades["Shimmering veil [off]"]?.bought) {
    const offer = o.shop.upgrades.find(
      (u) => u.name === "Shimmering veil [off]",
    );
    if (!offer) return wait("Allow the native veil toggle to rebuild.");
    if (offer.price !== 0 || !offer.canBuy)
      return answer(
        "blocked",
        "The native veil rebuy is not free and available.",
      );
    return act("Buy the visible zero-price veil toggle.", {
      type: "buy-upgrade",
      id: offer.id,
    });
  }
  if (o.elapsedMs < (m.nextClickAt || 0))
    return wait("Keep the native accepted-click cadence.");
  m.phase = "clicked";
  m.nextClickAt = o.elapsedMs + 34;
  return act(
    "Make the next direct native veil click, without selecting its seed or outcome.",
    { type: "click" },
  );
}
export function veilPolicySource(options = {}) {
  return `(function(o,actions,memory){return (${veilDecision.toString()})(o,memory,${JSON.stringify(options)});})`;
}
export function decideVeil(o, m = {}, options = {}) {
  return veilDecision(o, m, options);
}

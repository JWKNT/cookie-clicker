/** Return a market control only when its rendered ancestors are visible. */
export function VisibleMarketControl(id) {
  const element = l(id);
  if (!element) return null;
  for (let node = element; node; node = node.parentElement || node.parentNode) {
    const style = typeof getComputedStyle === 'function' && node.nodeType === 1
      ? getComputedStyle(node) : node.style;
    if (style && (style.display === 'none' || style.visibility === 'hidden' || style.visibility === 'collapse')) return null;
  }
  return element;
}

/** Open the Bank panel, then allow its next native draw to update controls. */
export function OpenMarketPanel() {
  const bank = Game.Objects.Bank;
  if (!bank.minigameLoaded || !bank.minigame || Game.ascensionMode !== 0
    || Game.OnAscend || Game.AscendTimer > 0 || Game.ReincarnateTimer > 0
    || Game.promptOn || Game.onMenu) return false;
  if (bank.onMinigame) return true;
  const button = VisibleMarketControl(`productMinigameButton${bank.id}`);
  if (typeof button?.click !== 'function') return false;
  button.click();
  return false;
}

/** Use the native visible loan button, including its sound and pointer effects. */
export function ClickMarketLoan(id) {
  if (!Number.isInteger(id) || id < 1 || id > 3 || !OpenMarketPanel()) return false;
  const M = Game.Objects.Bank.minigame;
  if (M.officeLevel < [2, 4, 5][id - 1]
    || Game.hasBuff(`Loan ${id}`) || Game.hasBuff(`Loan ${id} (interest)`)) return false;
  const button = VisibleMarketControl(`bankLoan${id}`);
  if (typeof button?.click !== 'function') return false;
  button.click();
  return !!Game.hasBuff(`Loan ${id}`);
}

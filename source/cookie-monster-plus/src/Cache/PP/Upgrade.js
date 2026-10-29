import GetWrinkConfigBank from '../../Disp/HelperFunctions/GetWrinkConfigBank.js';
import { CacheUpgrades } from '../VariablesAndData.js';
import { AutoplayIncome, AutoplayUpgradeValue } from './AutoplayValue.js';
import ColourOfPP from './ColourOfPP.js';

/**
 * This functions caches the PP of each upgrade and stores it in CM.Cache.Upgrades
 * With auto-click or auto golden cookies on, click and golden cookie upgrades are valued at what they
 * bring under autoplay (stored as autoValue) instead of being gray
 * It is called by CM.Cache.CachePP()
 */
export default function CacheUpgradePP() {
  const { settings } = Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod;
  const autoplay = settings.AutoClick || settings.AutoGolden;
  const income = autoplay ? AutoplayIncome() : Game.cookiesPs;
  const bank = Game.cookies + GetWrinkConfigBank();
  Object.keys(CacheUpgrades).forEach((i) => {
    const price = Game.Upgrades[i].getPrice();
    let value = CacheUpgrades[i].bonus;
    delete CacheUpgrades[i].autoValue;
    if (autoplay) {
      const autoValue = AutoplayUpgradeValue(i, CacheUpgrades[i], income, bank);
      if (autoValue > (value || 0)) {
        CacheUpgrades[i].autoValue = autoValue;
        value = autoValue;
      }
    }
    if (income) {
      CacheUpgrades[i].pp = Math.max(price - bank, 0) / income + price / value;
    } else CacheUpgrades[i].pp = price / value;
    if (Number.isNaN(CacheUpgrades[i].pp)) CacheUpgrades[i].pp = Infinity;

    CacheUpgrades[i].colour = ColourOfPP(CacheUpgrades[i], price);
  });
}

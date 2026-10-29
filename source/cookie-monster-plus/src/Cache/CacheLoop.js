import FormatTime from '../Disp/BeautifyAndFormatting/FormatTime.js';
import GetCPS from '../Disp/HelperFunctions/GetCPS.js';
import CacheAvgCPS from './CPS/CPS.js';
import CacheCurrWrinklerCPS from './CPS/CurrWrinklerCPS.js';
import CachePP from './PP/PP.js';
import CacheAscension from './Stats/Ascension.js';
import CacheHeavenlyChipsPS from './Stats/HeavenlyChips.js';
import AllAmountTillNextAchievement from './TillNextAchievement/AllAmountTillNextAchievement.js';
import { CacheTimeTillNextPrestige } from './VariablesAndData.js'; // eslint-disable-line no-unused-vars
import CacheWrinklers from './Wrinklers/Wrinklers.js';

/**
 * This functions caches variables that are needed every loop
 * @global	{string}	CM.Cache.TimeTillNextPrestige	Time requried till next prestige level
 */
export default function LoopCache() {
  // Update Wrinkler Bank
  CacheWrinklers();

  CachePP();
  AllAmountTillNextAchievement(false);
  CacheCurrWrinklerCPS();
  CacheAvgCPS();
  CacheHeavenlyChipsPS();
  CacheAscension();

  const cookiesToNext =
    Game.HowManyCookiesReset(
      Math.floor(Game.HowMuchPrestige(Game.cookiesReset + Game.cookiesEarned)) + 1,
    ) -
    (Game.cookiesEarned + Game.cookiesReset);
  CacheTimeTillNextPrestige = FormatTime(cookiesToNext / GetCPS());
}

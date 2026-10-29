import GetCPS from '../../Disp/HelperFunctions/GetCPS.js';
import FillCMDCache from '../FillCMDCache.js';
import { CacheHCPerSecond, CacheLastHeavenlyChips } from '../VariablesAndData.js';

/**
 * This functions caches the prestige levels ascending would grant and the rate at which they grow
 * It is called by CM.Cache.LoopCache()
 * @global	{number}	CM.Cache.LastHeavenlyChips	Prestige levels gained by ascending now
 * @global	{number}	CM.Cache.HCPerSecond		Heavenly chips gained per second at the current CPS
 */
export default function CacheHeavenlyChipsPS() {
  const total = Game.cookiesReset + Game.cookiesEarned;
  CacheLastHeavenlyChips =
    Math.floor(Game.HowMuchPrestige(total)) - Math.floor(Game.HowMuchPrestige(Game.cookiesReset));

  // Exact rate instead of differencing the floored level: d/dt cbrt(total / 1e12) = P / (3 * total) * CPS
  CacheHCPerSecond = total > 0 ? (Game.HowMuchPrestige(total) * GetCPS()) / (3 * total) : 0;

  FillCMDCache({ CacheLastHeavenlyChips, CacheHCPerSecond });
}

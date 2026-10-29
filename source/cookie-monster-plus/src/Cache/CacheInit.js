import { ClickTimes } from '../Disp/VariablesAndData.js';
import { CMAvgQueue, InitCookiesDiff } from './CPS/AverageQueue.js';
import CacheAvgCPS from './CPS/CPS.js';
import CacheNoGoldSwitchCPS from './CPS/NoGoldSwitchCPS.js';
import CacheDragonAuras from './Dragon/CacheDragonAuras.js';
import CachePP from './PP/PP.js';
import { CacheBuildingsPrices, CacheIncome } from './PriceAndIncome/PriceAndIncome.js';
import { CacheChain } from './Stats/ChainCookies.js';
import CacheHeavenlyChipsPS from './Stats/HeavenlyChips.js';
import CacheAllMissingUpgrades from './Stats/MissingUpgrades.js';
import CacheSeasonSpec from './Stats/Reindeer.js';
import { CacheGoldenAndWrathCookiesMults, CacheStatsCookies } from './Stats/Stats.js';
import AllAmountTillNextAchievement from './TillNextAchievement/AllAmountTillNextAchievement.js';
import { CacheAverageCookiesFromClicks } from './VariablesAndData.js'; // eslint-disable-line no-unused-vars
import CacheAscension from './Stats/Ascension.js';
import CacheWrinklers from './Wrinklers/Wrinklers.js';
import { SimDoSims } from '../Sim/VariablesAndData.js'; // eslint-disable-line no-unused-vars

/**
 * This functions runs all cache-functions to generate all "full" cache
 */
export default function InitCache() {
  CacheDragonAuras();
  CacheWrinklers();
  // The "Lucky!" values are based on CpS without the golden switch, so it has to come first
  CacheNoGoldSwitchCPS();
  CacheStatsCookies();
  CacheGoldenAndWrathCookiesMults();
  CacheChain();
  CacheAllMissingUpgrades();
  CacheSeasonSpec();
  InitCookiesDiff();
  CacheAverageCookiesFromClicks = new CMAvgQueue(ClickTimes[ClickTimes.length - 1] * 20);
  CacheHeavenlyChipsPS();
  AllAmountTillNextAchievement();
  CacheAvgCPS();
  CacheIncome();
  CacheBuildingsPrices();
  CachePP();
  CacheAscension(true);
  // Have the main loop recompute everything once before autoplay acts on these values
  SimDoSims = 1;
}

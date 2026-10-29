import InitCache from '../Cache/CacheInit.js';
import LoopCache from '../Cache/CacheLoop.js';
import CacheNoGoldSwitchCPS from '../Cache/CPS/NoGoldSwitchCPS.js';
import CacheSellAllForChoEgg from '../Cache/CPS/SellChoEgg.js';
import CacheDragonCost from '../Cache/Dragon/Dragon.js';
import CachePantheonGods from '../Cache/PantheonGods/CacheGods.js';
import { CacheBuildingsPrices, CacheIncome } from '../Cache/PriceAndIncome/PriceAndIncome.js';
import { CacheChain } from '../Cache/Stats/ChainCookies.js';
import CacheAllMissingUpgrades from '../Cache/Stats/MissingUpgrades.js';
import CacheSeasonSpec from '../Cache/Stats/Reindeer.js';
import { CacheGoldenAndWrathCookiesMults, CacheStatsCookies } from '../Cache/Stats/Stats.js';
import AllAmountTillNextAchievement from '../Cache/TillNextAchievement/AllAmountTillNextAchievement.js';
import { CacheDoRemakeBuildPrices, CacheHadBuildAura } from '../Cache/VariablesAndData.js';
import UpdateAscendState from '../Disp/HelperFunctions/UpdateAscendState.js';
import { LastAscendState } from '../Disp/VariablesAndData.js';
import InitData from '../Sim/InitializeData/InitData.js';
import { SimDoSims } from '../Sim/VariablesAndData.js';
import Autoplay from './Autoplay/Autoplay.js';
import CheckAscensionReady from './CheckStates/Ascension.js';
import CheckGardenTick from './CheckStates/Garden.js';
import CheckGoldenCookie from './CheckStates/GoldenCookie.js';
import CheckMagicMeter from './CheckStates/Grimoire.js';
import CheckSeasonPopup from './CheckStates/Season.js';
import CheckTickerFortune from './CheckStates/Ticker.js';
import CheckWrinklerCount from './CheckStates/Wrinkler.js';
import { LastModCount } from './VariablesAndData.js';

/**
 * Main loop of Cookie Monster
 * CM.init registers it to the "logic" hook provided by the modding api
 */
export default function CMLoopHook() {
  Autoplay();
  if (LastAscendState !== Game.OnAscend) {
    LastAscendState = Game.OnAscend;
    UpdateAscendState();
  }
  if (!Game.OnAscend && Game.AscendTimer === 0) {
    // Check if any other mods have been loaded
    if (LastModCount !== Object.keys(Game.mods).length) {
      InitData();
      InitCache();
      LastModCount = Object.keys(Game.mods).length;
    }

    // CM.Sim.DoSims is set whenever CPS has changed
    if (SimDoSims) {
      AllAmountTillNextAchievement(true);
      CacheIncome();

      CacheNoGoldSwitchCPS(); // Needed first
      CacheGoldenAndWrathCookiesMults();
      CacheStatsCookies();
      CacheAllMissingUpgrades();
      CacheChain();
      CacheDragonCost();
      CachePantheonGods();

      CacheSeasonSpec();
      CacheSellAllForChoEgg();

      SimDoSims = 0;
    }

    // Check for aura change to recalculate buildings prices
    const hasBuildAura = Game.auraMult('Fierce Hoarder') > 0;
    if (!CacheHadBuildAura && hasBuildAura) {
      CacheHadBuildAura = true;
      CacheDoRemakeBuildPrices = 1;
    } else if (CacheHadBuildAura && !hasBuildAura) {
      CacheHadBuildAura = false;
      CacheDoRemakeBuildPrices = 1;
    }

    if (CacheDoRemakeBuildPrices) {
      CacheBuildingsPrices();
      CacheDoRemakeBuildPrices = 0;
    }

    LoopCache();

    // Check all changing minigames and game-states
    CheckTickerFortune();
    CheckSeasonPopup();
    CheckGardenTick();
    CheckMagicMeter();
    CheckWrinklerCount();
    CheckAscensionReady();
  }
  // To remove Timers when ascending
  CheckGoldenCookie();
}

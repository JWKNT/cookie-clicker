import CalcNoGoldSwitchCPS from '../../Sim/Calculations/NoGoldenSwitchCalc.js';
import FillCMDCache from '../FillCMDCache.js';
import { CacheNoGoldSwitchCookiesPS } from '../VariablesAndData.js';

/**
 * This function calculates CPS without the Golden Switch as it might be needed in other functions
 * If so it CM.Sim.Win()'s them and the caller function will know to recall CM.Sim.CalculateGains()
 * It is called at the end of any functions that simulates certain behaviour
 */
export default function CacheNoGoldSwitchCPS() {
  if (Game.Has('Golden switch [off]')) {
    CacheNoGoldSwitchCookiesPS = CalcNoGoldSwitchCPS();
  } else CacheNoGoldSwitchCookiesPS = Game.cookiesPs;

  FillCMDCache({ CacheNoGoldSwitchCookiesPS });
}

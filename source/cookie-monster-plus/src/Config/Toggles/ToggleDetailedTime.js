import { CMSayTime } from '../../Disp/VariablesAndData.js';
import { BackupFunctions } from '../../Main/VariablesAndData.js';

/**
 * This function changes some of the time-displays in the game to be more detailed
 * It is called by a change in CM.Options.DetailedTime
 */
export default function ToggleDetailedTime() {
  if (Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod.settings.DetailedTime === 1)
    Game.sayTime = CMSayTime;
  else Game.sayTime = BackupFunctions.sayTime;
}

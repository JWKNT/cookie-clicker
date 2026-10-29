import { UpdateBotBar } from '../../Disp/InfoBars/BottomBar.js';
import { UpdateBotTimerBarPosition } from '../SpecificToggles.js';

/**
 * This function toggle the bottom bar
 * It is called by CM.Disp.UpdateAscendState() and a change in Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod.settings.BotBar
 */
export default function ToggleBotBar() {
  if (Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod.settings.BotBar === 1) {
    l('CMBotBar').style.display = '';
    UpdateBotBar();
  } else {
    l('CMBotBar').style.display = 'none';
  }
  UpdateBotTimerBarPosition();
}

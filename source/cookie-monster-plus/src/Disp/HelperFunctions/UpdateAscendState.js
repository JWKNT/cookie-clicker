import { ToggleTimerBar } from '../../Config/SpecificToggles.js';
import ToggleBotBar from '../../Config/Toggles/ToggleBotBar.js';

import UpdateBackground from './UpdateBackground.js';

/**
 * This function disables and shows the bars created by CookieMonster when the game is "ascending"
 * It is called by CM.Disp.Draw()
 */
export default function UpdateAscendState() {
  if (Game.OnAscend) {
    l('game').style.bottom = '0px';
    if (Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod.settings.BotBar === 1)
      l('CMBotBar').style.display = 'none';
    if (Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod.settings.TimerBar === 1)
      l('CMTimerBar').style.display = 'none';
  } else {
    ToggleBotBar();
    ToggleTimerBar();
  }
  UpdateBackground();
}

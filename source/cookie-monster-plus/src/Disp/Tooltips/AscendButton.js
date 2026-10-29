import {
  CacheHCPerSecond,
  CacheLastHeavenlyChips,
  CacheTimeTillNextPrestige,
} from '../../Cache/VariablesAndData.js';
import Beautify from '../BeautifyAndFormatting/Beautify.js';
import AscensionSummary, { FormatPercent } from '../HelperFunctions/AscensionSummary.js';
import { ColourTextPre } from '../VariablesAndData.js';

/**
 * This function replaces the tooltip of the ascend button
 */
export default function ReplaceAscendTooltip() {
  const cookiesToNext = Math.max(
    0,
    Game.HowManyCookiesReset(
      Math.floor(Game.HowMuchPrestige(Game.cookiesReset + Game.cookiesEarned)) + 1,
    ) -
      (Game.cookiesEarned + Game.cookiesReset),
  );

  const startDate = Game.sayTime(((Date.now() - Game.startDate) / 1000) * Game.fps, -1);
  let str = `You've been on this run for <b>${
    startDate === '' ? 'not very long' : startDate
  }</b>.<br>
  <div class="line"></div>`;
  if (Game.prestige > 0) {
    str += `Your prestige level is currently <b>${Beautify(Game.prestige)}</b>.<br>(CpS +${Beautify(
      Game.prestige,
    )}%)
    <div class="line"></div>`;
  }
  if (CacheLastHeavenlyChips < 1) str += 'Ascending now would grant you no prestige.';
  else if (CacheLastHeavenlyChips < 2)
    str +=
      'Ascending now would grant you<br><b>1 prestige level</b> (+1% CpS)<br>and <b>1 heavenly chip</b> to spend.';
  else
    str += `Ascending now would grant you<br><b>${Beautify(
      CacheLastHeavenlyChips,
    )} prestige levels</b> (+${Beautify(CacheLastHeavenlyChips)}% CpS)<br>and <b>${Beautify(
      CacheLastHeavenlyChips,
    )} heavenly chips</b> to spend.`;
  str += `<div class="line"></div>
  You need <b>${Beautify(cookiesToNext)} more cookies</b> for the next level.<br>
  ${
    Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod.settings.TooltipAscendButton
      ? `<div class='line'></div>It takes ${CacheTimeTillNextPrestige} to reach the next level and you are making ${Beautify(
          CacheHCPerSecond,
          2,
        )} chips per second.<br>`
      : ''
  }`;

  if (Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod.settings.AscendAdvisor) {
    const summary = AscensionSummary();
    if (summary.status !== 'na' && summary.status !== 'early') {
      str += `<div class="line"></div><b class="${ColourTextPre}${summary.colour}">${summary.headline}</b>`;
      if (summary.status === 'wait')
        str += `<br>Waiting for <b>+${Beautify(summary.levelsAtTarget)} levels</b> (+${FormatPercent(
          summary.speedGainAtTarget * 100,
        )} production) instead of ascending now for +${FormatPercent(summary.speedGainNow * 100)}.`;
    }
  }
  l('ascendTooltip').innerHTML = str;
}

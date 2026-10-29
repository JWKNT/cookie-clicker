import { notificationsFunctions as nF } from '@cookiemonsterteam/cookiemonsterframework/src/index.js';
import { AscensionCache } from '../../Cache/Stats/Ascension.js';
import Beautify from '../../Disp/BeautifyAndFormatting/Beautify.js';
import { FormatPercent } from '../../Disp/HelperFunctions/AscensionSummary.js';

/** Seconds the plan has to keep saying "ascend now" before acting on it */
export const SUSTAIN_SECONDS = 10;

/** Start date of the run that has been alerted, and since when the current run has been ready */
let AlertedRun = null;
let ReadySince = null;

/**
 * Seconds for which the plan has continuously said to ascend now (0 when it does not)
 * @returns	{number}
 */
export function ReadySeconds() {
  return ReadySince === null ? 0 : (Date.now() - ReadySince) / 1000;
}

/**
 * This function tracks whether ascending is optimal and alerts once per run when it becomes so
 * It is called by CM.Main.Loop
 */
export default function CheckAscensionReady() {
  const { applicable, plan } = AscensionCache;
  if (
    !applicable ||
    plan === null ||
    !plan.applicable ||
    Game.OnAscend ||
    Game.AscendTimer > 0 ||
    window.cookieMonsterFrameworkData.isInitializing
  ) {
    ReadySince = null;
    return;
  }
  if (!plan.ascendNow || plan.levelsNow < 1) {
    ReadySince = null;
    return;
  }
  if (ReadySince === null) ReadySince = Date.now();
  if (ReadySeconds() < SUSTAIN_SECONDS || AlertedRun === Game.startDate) return;

  AlertedRun = Game.startDate;
  const { settings } = Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod;
  if (settings.AutoAscend) return; // Autoplay ascends by itself
  const message = `Ascending now grants ${Beautify(plan.levelsNow)} prestige level${
    plan.levelsNow === 1 ? '' : 's'
  } (+${FormatPercent(plan.speedGainNow * 100)} production in every future run).`;
  nF.createFlash('cookieMonsterMod', 3, 'AscendFlash', false);
  nF.playCMSound('cookieMonsterMod', settings.AscendSoundURL, 'AscendSound', 'AscendVolume', false);
  nF.createNotification('cookieMonsterMod', 'AscendNotification', 'Time to ascend', message);
  if (settings.AscendNote)
    Game.Notify(
      'Optimal time to ascend',
      `${message}<br>Pop wrinklers and buy the Chocolate egg (if unlocked) first.`,
      [19, 7],
    );
}

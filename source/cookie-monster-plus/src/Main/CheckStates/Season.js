import { notificationsFunctions as nF } from '@cookiemonsterteam/cookiemonsterframework/src/index.js';
import { CacheSeasonPopShimmer } from '../../Cache/VariablesAndData.js'; // eslint-disable-line no-unused-vars
import { LastSeasonPopupState } from '../VariablesAndData.js';
import { resetChanceTotalDeer } from './Probability.js';

/**
 * This function checks if there is reindeer that has spawned
 * It is called by CM.Main.Loop
 */
export default function CheckSeasonPopup() {
  if (LastSeasonPopupState !== Game.shimmerTypes.reindeer.spawned) {
    LastSeasonPopupState = Game.shimmerTypes.reindeer.spawned;
    Object.keys(Game.shimmers).forEach((i) => {
      if (Game.shimmers[i].spawnLead && Game.shimmers[i].type === 'reindeer') {
        CacheSeasonPopShimmer = Game.shimmers[i];
      }
    });
    nF.createFlash('cookieMonsterMod', 3, 'SeaFlash', false);
    nF.playCMSound(
      'cookieMonsterMod',
      Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod.settings.SeaSoundURL,
      'SeaSound',
      'SeaVolume',
      false,
    );
    nF.createNotification(
      'cookieMonsterMod',
      'SeaNotification',
      'Reindeer sighted!',
      'A Reindeer has spawned. Click it now!',
    );
    // Reset the cumulative probability when a deer is spawned
    resetChanceTotalDeer();
  }
}

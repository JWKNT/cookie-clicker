import { notificationsFunctions as nF } from '@cookiemonsterteam/cookiemonsterframework/src/index.js';
import {
  CacheSpawnedGoldenShimmer, // eslint-disable-line no-unused-vars
  CacheGoldenShimmersByID,
} from '../../Cache/VariablesAndData.js';
import CreateGCTimer from '../../Disp/GoldenCookieTimers/GoldenCookieTimers.js';
import { UpdateFavicon } from '../../Disp/TabTitle/FavIcon.js';
import { GCTimers } from '../../Disp/VariablesAndData.js';
import {
  CurrSpawnedGoldenCookieState,
  LastGoldenCookieState,
  LastSpawnedGoldenCookieState,
} from '../VariablesAndData.js';
import { resetChanceTotal } from './Probability.js';

/**
 * Auxilirary function that finds all currently spawned shimmers.
 * CM.Cache.spawnedGoldenShimmer stores the non-user spawned cookie to later determine data for the favicon and tab-title
 * It is called by CM.CM.Main.CheckGoldenCookie
 */
function FindShimmer() {
  CurrSpawnedGoldenCookieState = 0;
  CacheGoldenShimmersByID = {};
  Object.keys(Game.shimmers).forEach((i) => {
    CacheGoldenShimmersByID[Game.shimmers[i].id] = Game.shimmers[i];
    if (Game.shimmers[i].spawnLead && Game.shimmers[i].type === 'golden') {
      CacheSpawnedGoldenShimmer = Game.shimmers[i];
      CurrSpawnedGoldenCookieState += 1;
    }
  });
}

/**
 * This function checks for changes in the amount of Golden Cookies
 * It is called by CM.Main.Loop
 */
export default function CheckGoldenCookie() {
  FindShimmer();
  Object.keys(GCTimers).forEach((i) => {
    if (typeof CacheGoldenShimmersByID[i] === 'undefined') {
      GCTimers[i].parentNode.removeChild(GCTimers[i]);
      delete GCTimers[i];
    }
  });
  if (LastGoldenCookieState !== Game.shimmerTypes.golden.n) {
    LastGoldenCookieState = Game.shimmerTypes.golden.n;
    if (LastGoldenCookieState) {
      if (LastSpawnedGoldenCookieState < CurrSpawnedGoldenCookieState) {
        // Autoplay pops golden cookies itself, so it needs no alerts
        if (!Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod.settings.AutoGolden) {
          nF.createFlash('cookieMonsterMod', 3, 'GCFlash', false);
          nF.playCMSound(
            'cookieMonsterMod',
            Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod.settings.GCSoundURL,
            'GCSound',
            'GCVolume',
            false,
          );
          nF.createNotification(
            'cookieMonsterMod',
            'GCNotification',
            'Golden Cookie Spawned',
            'A Golden Cookie has spawned. Click it now!',
          );
        }
        // Reset the cumulative probability when a GC has spawned
        resetChanceTotal();
      }

      Object.keys(Game.shimmers).forEach((i) => {
        if (typeof GCTimers[Game.shimmers[i].id] === 'undefined') {
          CreateGCTimer(Game.shimmers[i]);
        }
      });
    }
    UpdateFavicon();
    LastSpawnedGoldenCookieState = CurrSpawnedGoldenCookieState;
    if (CurrSpawnedGoldenCookieState === 0) CacheSpawnedGoldenShimmer = 0;
  } else if (
    Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod.settings.GCTimer === 1 &&
    LastGoldenCookieState
  ) {
    Object.keys(GCTimers).forEach((i) => {
      GCTimers[i].style.opacity = CacheGoldenShimmersByID[i].l.style.opacity;
      GCTimers[i].style.transform = CacheGoldenShimmersByID[i].l.style.transform;
      GCTimers[i].textContent = Math.ceil(CacheGoldenShimmersByID[i].life / Game.fps);
    });
  }
}

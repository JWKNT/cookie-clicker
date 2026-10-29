import init from './InitSaveLoad/init.js';
import load from './InitSaveLoad/load.js';
import save from './InitSaveLoad/save.js';

const CM = {
  init,
  load,
  save,
  cookieMonsterPlus: true,
};

// Cookie Monster+ replaces the original mod: if the Workshop "Cookie Monster" is enabled as well,
// its registration (which happens later, after a network load) is skipped so only one copy runs
const { registerMod } = Game;
Game.registerMod = function (id, mod) {
  if (id === 'CookieMonster' && !mod.cookieMonsterPlus) {
    console.log('Cookie Monster+ is active, skipping the original Cookie Monster'); // eslint-disable-line no-console
    return false;
  }
  return registerMod.apply(this, [id, mod]);
};

if (typeof Steam !== 'undefined') {
  // Need to add a delay for steam
  setTimeout(() => {
    Game.registerMod('CookieMonster', CM);

    // Game.registerMod also calls CM.load() which calls the loop hook
    // Thus sounds normally play at start up as Season and Garden states are checked
    window.cookieMonsterFrameworkData.isInitializing = false;
  }, 2000);
} else {
  Game.registerMod('CookieMonster', CM);
  window.cookieMonsterFrameworkData.isInitializing = false;
}

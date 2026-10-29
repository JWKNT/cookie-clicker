import { initFunctions } from '@cookiemonsterteam/cookiemonsterframework';
import CMDrawHook from '../Disp/DrawHook.js';
import CMClickHook from '../Main/ClickHook.js';
import InitializeCookieMonster from '../Main/Initialization.js';
import CMLoopHook from '../Main/LoopHook.js';
import load from './load.js';

/**
 * This creates a init function for the CM object. Per Game code/comments:
 * "this function is called as soon as the mod is registered
 * declare hooks here"
 * It starts the further initialization of CookieMonster and registers hooks
 */
export default function init() {
  // Load Cookie Monster Mod Framework and register mod
  initFunctions.initModFramework();
  window.cookieMonsterFrameworkData.isInitializing = true;
  initFunctions.registerMod('cookieMonsterMod');

  InitializeCookieMonster();
  Game.registerHook('click', CMClickHook);
  Game.registerHook('draw', CMDrawHook);
  Game.registerHook('logic', CMLoopHook);

  // Load default settings if no previous saveData is found
  if (typeof Game.modSaveData.cookieMonsterMod === 'undefined') {
    load('{}');
  }
}

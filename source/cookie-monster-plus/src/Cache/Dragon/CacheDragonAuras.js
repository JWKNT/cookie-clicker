import { CacheDragonAura, CacheDragonAura2 } from '../VariablesAndData.js'; // eslint-disable-line no-unused-vars

/**
 * This functions caches the currently selected Dragon Auras
 */
export default function CacheDragonAuras() {
  CacheDragonAura = Game.dragonAura;
  CacheDragonAura2 = Game.dragonAura2;
}

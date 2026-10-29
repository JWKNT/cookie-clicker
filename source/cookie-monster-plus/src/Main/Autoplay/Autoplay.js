import AutoAchievements from './AutoAchievements.js';
import AutoAscend from './AutoAscend.js';
import AutoBuy from './AutoBuy.js';
import UpdateAutoClicker from './AutoClick.js';
import AutoDragon from './AutoDragon.js';
import AutoElder from './AutoElder.js';
import AutoGarden from './AutoGarden.js';
import AutoGodzamok from './AutoGodzamok.js';
import AutoGolden from './AutoGolden.js';
import AutoGrimoire from './AutoGrimoire.js';
import AutoLumps from './AutoLumps.js';
import AutoMarket from './AutoMarket.js';
import AutoPantheon from './AutoPantheon.js';
import AutoSeasons from './AutoSeasons.js';
import { ChallengeRun } from './Challenge.js';

/** The other systems take turns on the frames between purchases */
const SYSTEMS = [
  AutoElder,
  AutoDragon,
  AutoSeasons,
  AutoLumps,
  AutoPantheon,
  AutoGrimoire,
  AutoGarden,
  AutoMarket,
  AutoAchievements,
];
/** Purchases are spaced by a few frames so Cookie Monster's caches catch up after each one */
const CYCLE_FRAMES = SYSTEMS.length + 1;

/**
 * Runs Cookie Monster+'s autoplay: clicking, golden cookies, Godzamok combos, purchases, the
 * Grandmapocalypse, the dragon, seasons, sugar lumps, the Pantheon, Grimoire, Garden and Stock Market,
 * easy achievements and ascensions
 * It is called every logic frame by CM.Main.Loop, including while ascending
 */
export default function Autoplay() {
  if (Game.T % Game.fps === 0) UpdateAutoClicker();
  AutoGolden();
  const turn = Game.T % CYCLE_FRAMES;
  if (ChallengeRun()) {
    // A Born again run has no minigames, lumps or seasons, and its rules forbid upgrades
    if (turn === 0) AutoBuy();
  } else {
    AutoGodzamok();
    if (turn === 0) AutoBuy();
    else SYSTEMS[turn - 1]();
  }
  AutoAscend();
}

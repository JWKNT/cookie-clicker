/** Functions related to the Timer Bar */

import { UpdateBotTimerBarPosition } from '../../Config/SpecificToggles.js';
import { AutoBuyState } from '../../Main/Autoplay/AutoBuy.js';
import Beautify from '../BeautifyAndFormatting/Beautify.js';
import ShortDuration from '../BeautifyAndFormatting/ShortDuration.js';
import AscensionSummary from '../HelperFunctions/AscensionSummary.js';
import {
  BuffColours,
  ColourBackPre,
  ColourBlue,
  ColourGreen,
  ColourGray,
  ColourOrange,
  ColourPurple,
  ColourYellow,
  LastNumberOfTimers,
} from '../VariablesAndData.js';
import { CreateTimer } from './CreateDOMElements.js';
import { updateChanceTotal, updateChanceTotalDeer } from '../../Main/CheckStates/Probability.js';

/**
 * This function creates the TimerBar and appends it to l('wrapper')
 */
export function CreateTimerBar() {
  const TimerBar = document.createElement('div');
  TimerBar.id = 'CMTimerBar';
  TimerBar.style.position = 'absolute';
  TimerBar.style.display = 'none';
  TimerBar.style.height = '0px';
  TimerBar.style.fontSize = '10px';
  TimerBar.style.fontWeight = 'bold';
  TimerBar.style.backgroundColor = 'black';

  // Create standard Autosave bar
  const CMTimerBarAutosave = CreateTimer('CMTimerBarAutosave', 'Autosave', [
    { id: 'CMTimerBarAutosaveBar', colour: ColourPurple },
  ]);
  TimerBar.appendChild(CMTimerBarAutosave);

  // Create ascension readiness bar
  const CMTimerBarAscend = CreateTimer('CMTimerBarAscend', 'Ascend', [
    { id: 'CMTimerBarAscendBar', colour: ColourBlue },
  ]);
  TimerBar.appendChild(CMTimerBarAscend);

  // Create autoplay "Lucky!" bank bar, shown while the buyer keeps cookies back for "Lucky!"
  const CMTimerBarLuckyBank = CreateTimer('CMTimerBarLuckyBank', 'Lucky! bank', [
    { id: 'CMTimerBarLuckyBankBar', colour: ColourYellow },
  ]);
  TimerBar.appendChild(CMTimerBarLuckyBank);

  // Create autoplay purchase bar
  const CMTimerBarAutoBuy = CreateTimer('CMTimerBarAutoBuy', 'Next buy', [
    { id: 'CMTimerBarAutoBuyBar', colour: ColourGreen },
  ]);
  TimerBar.appendChild(CMTimerBarAutoBuy);

  // Create standard Golden Cookie bar
  const CMTimerBarGC = CreateTimer('CMTimerBarGC', 'Next Cookie', [
    { id: 'CMTimerBarGCMinBar', colour: ColourGray },
    { id: 'CMTimerBarGCBar', colour: ColourPurple },
  ]);
  TimerBar.appendChild(CMTimerBarGC);

  // Create standard Reindeer bar
  const CMTimerBarRen = CreateTimer('CMTimerBarRen', 'Next Reindeer', [
    { id: 'CMTimerBarRenMinBar', colour: ColourGray },
    { id: 'CMTimerBarRenBar', colour: ColourOrange },
  ]);
  TimerBar.appendChild(CMTimerBarRen);
  const TimerBarBuffTimers = document.createElement('div');
  TimerBarBuffTimers.id = 'CMTimerBarBuffTimers';
  TimerBar.appendChild(TimerBarBuffTimers);

  l('wrapper').appendChild(TimerBar);
}

/**
 * This function updates indivudual timers in the timer bar
 */
export function UpdateTimerBar() {
  if (Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod.settings.TimerBar === 1) {
    // label width: 113, timer width: 30, div margin: 20
    const maxWidthTwoBar = l('CMTimerBar').offsetWidth - 163;
    // label width: 113, div margin: 20, calculate timer width at runtime
    const maxWidthOneBar = l('CMTimerBar').offsetWidth - 133;
    let numberOfTimers = 0;

    if (
      Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod.settings.AutosaveTimerBar &&
      Game.prefs.autosave
    ) {
      const timeTillNextAutosave =
        (Game.fps * 60 - (Game.OnAscend ? 0 : Game.T % (Game.fps * 60))) / Game.fps;
      l('CMTimerBarAutosave').style.display = '';
      l('CMTimerBarAutosaveBar').style.width = `${Math.round(
        (timeTillNextAutosave *
          (maxWidthOneBar - Math.ceil(timeTillNextAutosave).toString().length * 8)) /
          60,
      )}px`;
      if (
        Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod.settings.TimerBarOverlay >= 1
      ) {
        l('CMTimerBarAutosaveBar').textContent = Math.ceil(timeTillNextAutosave);
      } else l('CMTimerBarAutosaveBar').textContent = '';
      l('CMTimerBarAutosaveTime').textContent = Math.ceil(timeTillNextAutosave);
      numberOfTimers += 1;
    } else l('CMTimerBarAutosave').style.display = 'none';

    // Ascension readiness: fills up to the optimal ascension time
    const ascension = Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod.settings
      .AscendTimerBar
      ? AscensionSummary()
      : null;
    if (ascension !== null && (ascension.status === 'wait' || ascension.status === 'ready')) {
      const label = ascension.shortForecast;
      l('CMTimerBarAscend').style.display = '';
      l('CMTimerBarAscendBar').className = ColourBackPre + ascension.colour;
      l('CMTimerBarAscendBar').style.color = 'black';
      l('CMTimerBarAscendBar').style.width = `${Math.round(
        Math.min(ascension.readiness, 1) * (maxWidthOneBar - label.length * 7 - 8),
      )}px`;
      if (Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod.settings.TimerBarOverlay >= 1)
        l('CMTimerBarAscendBar').textContent =
          ascension.readiness >= 0.12
            ? `${Math.floor(Math.min(ascension.readiness, 9.99) * 100)}%`
            : '';
      else l('CMTimerBarAscendBar').textContent = '';
      l('CMTimerBarAscendTime').textContent = label;
      numberOfTimers += 1;
    } else l('CMTimerBarAscend').style.display = 'none';

    // Autoplay: what the buyer is saving for
    const next = Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod.settings.AutoBuy
      ? AutoBuyState.next
      : null;

    // The "Lucky!" bank kept back from that purchase, which is why an affordable item can wait
    if (next !== null && next.reason === 'lucky') {
      const banked = Math.min(Game.cookies, next.reserve);
      const label = `${Beautify(banked)} / ${Beautify(next.reserve)}`;
      l('CMTimerBarLuckyBank').style.display = '';
      l('CMTimerBarLuckyBankBar').style.width = `${Math.round(
        (banked / next.reserve) * Math.max(maxWidthOneBar - label.length * 6 - 8, 0),
      )}px`;
      l('CMTimerBarLuckyBankTime').textContent = label;
      numberOfTimers += 1;
    } else l('CMTimerBarLuckyBank').style.display = 'none';

    if (next !== null) {
      const name = next.name.length > 18 ? `${next.name.slice(0, 17)}…` : next.name;
      const time = next.eta > 0 ? ShortDuration(next.eta) : 'now';
      let label = `${time} ${name}`;
      if (next.reserve > 0 && Game.cookies >= next.price) {
        // Affordable, but the cookies are kept for the "Lucky!" bank or a seasonal action first; in a
        // narrow window the reason matters more than the name
        const why = next.reason === 'season' ? ' (season first)' : ' (Lucky! bank first)';
        label =
          (label.length + why.length) * 6 <= maxWidthOneBar - 8
            ? `${label}${why}`
            : `${time}${why}`;
      }
      l('CMTimerBarAutoBuy').style.display = '';
      l('CMTimerBarAutoBuyBar').style.width = `${Math.round(
        Math.min(Math.max(next.spendable / next.price, 0), 1) *
          Math.max(maxWidthOneBar - label.length * 6 - 8, 0),
      )}px`;
      l('CMTimerBarAutoBuyTime').textContent = label;
      numberOfTimers += 1;
    } else l('CMTimerBarAutoBuy').style.display = 'none';

    // Regulates visibility of Golden Cookie timer
    if (Game.shimmerTypes.golden.spawned === 0 && !Game.Has('Golden switch [off]')) {
      l('CMTimerBarGC').style.display = '';
      l('CMTimerBarGCMinBar').style.width = `${Math.round(
        (Math.max(0, Game.shimmerTypes.golden.minTime - Game.shimmerTypes.golden.time) *
          maxWidthTwoBar) /
          Game.shimmerTypes.golden.maxTime,
      )}px`;
      if (Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod.settings.TimerBarOverlay >= 1)
        l('CMTimerBarGCMinBar').textContent = Math.ceil(
          (Game.shimmerTypes.golden.minTime - Game.shimmerTypes.golden.time) / Game.fps,
        );
      else l('CMTimerBarGCMinBar').textContent = '';
      if (Game.shimmerTypes.golden.minTime === Game.shimmerTypes.golden.maxTime) {
        l('CMTimerBarGCMinBar').style.borderTopRightRadius = '10px';
        l('CMTimerBarGCMinBar').style.borderBottomRightRadius = '10px';
      } else {
        l('CMTimerBarGCMinBar').style.borderTopRightRadius = '';
        l('CMTimerBarGCMinBar').style.borderBottomRightRadius = '';
      }
      l('CMTimerBarGCBar').style.width = `${Math.round(
        (Math.min(
          Game.shimmerTypes.golden.maxTime - Game.shimmerTypes.golden.minTime,
          Game.shimmerTypes.golden.maxTime - Game.shimmerTypes.golden.time,
        ) *
          maxWidthTwoBar) /
          Game.shimmerTypes.golden.maxTime,
      )}px`;
      if (Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod.settings.TimerBarOverlay >= 1)
        l('CMTimerBarGCBar').textContent = Math.ceil(
          Math.min(
            Game.shimmerTypes.golden.maxTime - Game.shimmerTypes.golden.minTime,
            Game.shimmerTypes.golden.maxTime - Game.shimmerTypes.golden.time,
          ) / Game.fps,
        );
      else l('CMTimerBarGCBar').textContent = '';
      const chanceToSpawn =
        Math.max(
          0,
          (Game.shimmerTypes.golden.time - Game.shimmerTypes.golden.minTime) /
            (Game.shimmerTypes.golden.maxTime - Game.shimmerTypes.golden.minTime),
        ) ** 5;
      const finalChance = updateChanceTotal(chanceToSpawn);
      l('CMTimerBarGCTime').textContent = `${Math.ceil(
        (Game.shimmerTypes.golden.maxTime - Game.shimmerTypes.golden.time) / Game.fps,
      )} `;
      if (finalChance < 0.01) {
        l('CMTimerBarGCTime').textContent +=
          `<${(0.01).toLocaleString('en', { style: 'percent' })}`;
      } else {
        l('CMTimerBarGCTime').textContent += finalChance.toLocaleString('en', {
          style: 'percent',
        });
      }
      numberOfTimers += 1;
    } else l('CMTimerBarGC').style.display = 'none';

    // Regulates visibility of Reindeer timer
    if (Game.season === 'christmas' && Game.shimmerTypes.reindeer.spawned === 0) {
      l('CMTimerBarRen').style.display = '';
      l('CMTimerBarRenMinBar').style.width = `${Math.round(
        (Math.max(0, Game.shimmerTypes.reindeer.minTime - Game.shimmerTypes.reindeer.time) *
          maxWidthTwoBar) /
          Game.shimmerTypes.reindeer.maxTime,
      )}px`;
      if (Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod.settings.TimerBarOverlay >= 1)
        l('CMTimerBarRenMinBar').textContent = Math.ceil(
          (Game.shimmerTypes.reindeer.minTime - Game.shimmerTypes.reindeer.time) / Game.fps,
        );
      else l('CMTimerBarRenMinBar').textContent = '';
      l('CMTimerBarRenBar').style.width = `${Math.round(
        (Math.min(
          Game.shimmerTypes.reindeer.maxTime - Game.shimmerTypes.reindeer.minTime,
          Game.shimmerTypes.reindeer.maxTime - Game.shimmerTypes.reindeer.time,
        ) *
          maxWidthTwoBar) /
          Game.shimmerTypes.reindeer.maxTime,
      )}px`;
      if (Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod.settings.TimerBarOverlay >= 1)
        l('CMTimerBarRenBar').textContent = Math.ceil(
          Math.min(
            Game.shimmerTypes.reindeer.maxTime - Game.shimmerTypes.reindeer.minTime,
            Game.shimmerTypes.reindeer.maxTime - Game.shimmerTypes.reindeer.time,
          ) / Game.fps,
        );
      else l('CMTimerBarRenBar').textContent = '';
      const chanceToSpawn =
        Math.max(
          0,
          (Game.shimmerTypes.reindeer.time - Game.shimmerTypes.reindeer.minTime) /
            (Game.shimmerTypes.reindeer.maxTime - Game.shimmerTypes.reindeer.minTime),
        ) ** 5;
      const deerFinalChance = updateChanceTotalDeer(chanceToSpawn);
      l('CMTimerBarRenTime').textContent = `${Math.ceil(
        (Game.shimmerTypes.reindeer.maxTime - Game.shimmerTypes.reindeer.time) / Game.fps,
      )} `;
      if (deerFinalChance < 0.01) {
        l('CMTimerBarRenTime').textContent +=
          `<${(0.01).toLocaleString('en', { style: 'percent' })}`;
      } else {
        l('CMTimerBarRenTime').textContent += deerFinalChance.toLocaleString('en', {
          style: 'percent',
        });
      }
      numberOfTimers += 1;
    } else {
      l('CMTimerBarRen').style.display = 'none';
    }

    // On every frame all buff-timers are deleted and re-created
    const BuffTimerBars = {};
    l('CMTimerBarBuffTimers').innerHTML = '';
    Object.keys(Game.buffs).forEach((i) => {
      if (Game.buffs[i]) {
        const timer = CreateTimer(Game.buffs[i].name, Game.buffs[i].name, [
          { id: `${Game.buffs[i].name}Bar` },
        ]);
        timer.style.display = '';
        let classColour = '';
        // Gives specific timers specific colours
        if (typeof BuffColours[Game.buffs[i].name] !== 'undefined') {
          classColour = BuffColours[Game.buffs[i].name];
        } else classColour = ColourPurple;
        timer.lastChild.children[1].className = ColourBackPre + classColour;
        timer.lastChild.children[1].style.color = 'black';
        if (
          Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod.settings.TimerBarOverlay === 2
        )
          timer.lastChild.children[1].textContent = `${Math.round(
            100 * (Game.buffs[i].time / Game.buffs[i].maxTime),
          )}%`;
        else timer.lastChild.children[1].textContent = '';
        timer.lastChild.children[1].style.width = `${Math.round(
          (Game.buffs[i].time *
            (maxWidthOneBar - Math.ceil(Game.buffs[i].time / Game.fps).toString().length * 8)) /
            Game.buffs[i].maxTime,
        )}px`;
        timer.lastChild.children[2].textContent = Math.ceil(Game.buffs[i].time / Game.fps);
        numberOfTimers += 1;
        BuffTimerBars[Game.buffs[i].name] = timer;
      }
    });
    Object.keys(BuffTimerBars).forEach((i) => {
      l('CMTimerBarBuffTimers').appendChild(BuffTimerBars[i]);
    });

    if (numberOfTimers !== 0) {
      l('CMTimerBar').style.height = `${numberOfTimers * 12 + 2}px`;
    }
    if (LastNumberOfTimers !== numberOfTimers) {
      LastNumberOfTimers = numberOfTimers;
      UpdateBotTimerBarPosition();
    }
  }
}

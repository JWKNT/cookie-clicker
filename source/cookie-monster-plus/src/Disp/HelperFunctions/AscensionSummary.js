import { AscensionCache } from '../../Cache/Stats/Ascension.js';
import Beautify from '../BeautifyAndFormatting/Beautify.js';
import ShortDuration from '../BeautifyAndFormatting/ShortDuration.js';
import { ColourBlue, ColourGray, ColourGreen, ColourYellow } from '../VariablesAndData.js';

/**
 * Formats a percentage with two significant digits for small values
 * @param	{number}	value	Percentage
 * @returns	{string}
 */
export function FormatPercent(value) {
  if (!Number.isFinite(value)) return '∞%';
  if (value >= 100) return `${Beautify(Math.round(value), 0)}%`;
  if (value === 0) return '0%';
  return `${Number(value.toPrecision(2))}%`;
}

/**
 * Turns the cached advisor plan into the values shown in the stats page, timer bar and ascend tooltip
 * Statuses: 'na' (prestige has no effect), 'early' (run too young to plan), 'none' (no ascension worth
 * a 10% speed-up in sight), 'wait' (keep baking) and 'ready' (ascend now)
 * @returns	{object}	summary
 */
export default function AscensionSummary() {
  const { applicable, plan, state } = AscensionCache;
  if (!applicable) {
    return {
      status: 'na',
      headline:
        Game.ascensionMode === 1
          ? 'Prestige has no effect in Born again mode'
          : 'Prestige has no effect right now',
      colour: ColourGray,
    };
  }
  if (plan === null || !plan.applicable) {
    return { status: 'early', headline: 'Measuring this run…', colour: ColourGray };
  }

  if (!plan.targetFound) {
    return {
      status: 'none',
      headline: 'Keep baking: no ascension worth it is in sight yet',
      colour: ColourBlue,
      readiness: 0,
      levelsNow: plan.levelsNow,
      speedGainNow: plan.speedGainNow,
      beta: plan.beta,
      runTime: state.runTime,
      shortForecast: '∞',
    };
  }

  const low = Math.min(plan.remainingFast, plan.remainingSlow);
  const high = Math.max(plan.remainingFast, plan.remainingSlow);
  const forecastText =
    ShortDuration(low) === ShortDuration(high)
      ? `≈ ${ShortDuration(plan.remaining)}`
      : `${ShortDuration(low)} – ${ShortDuration(high)}`;

  let status = 'wait';
  let colour = ColourBlue;
  let headline = `Keep baking: optimal ascension in ${forecastText}`;
  if (plan.ascendNow) {
    status = 'ready';
    colour = ColourGreen;
    headline = 'Ascend now: it is the optimal time';
  } else if (plan.readiness >= 0.9) colour = ColourYellow;

  return {
    status,
    headline,
    colour,
    readiness: plan.readiness,
    levelsNow: plan.levelsNow,
    speedGainNow: plan.speedGainNow,
    levelsAtTarget: plan.levelsAtTarget,
    speedGainAtTarget: plan.speedGainAtTarget,
    costOfAscendingNow: plan.costOfAscendingNow,
    forecastText,
    shortForecast: plan.ascendNow ? 'NOW' : ShortDuration(plan.remaining),
    beta: plan.beta,
    runTime: state.runTime,
  };
}

/** Creates the "Ascension Advisor" section of the statistics page */

import { AscensionCache } from '../../../Cache/Stats/Ascension.js';
import { CacheLastChoEgg, CacheWrinklersTotal } from '../../../Cache/VariablesAndData.js';
import Beautify from '../../BeautifyAndFormatting/Beautify.js';
import ShortDuration from '../../BeautifyAndFormatting/ShortDuration.js';
import AscensionSummary, { FormatPercent } from '../../HelperFunctions/AscensionSummary.js';
import { ColourBackPre, ColourTextPre, SimpleTooltipElements } from '../../VariablesAndData.js';

/**
 * Creates a horizontal meter
 * @param	{number}	fraction	Filled fraction (0 to 1)
 * @param	{string}	colour		Colour name used by Cookie Monster colour classes
 * @param	{string}	label		Text drawn over the meter
 * @returns	{object}	div			The meter
 */
export function CreateMeter(fraction, colour, label) {
  const meter = document.createElement('div');
  meter.className = 'CMMeter';
  const fill = document.createElement('div');
  fill.className = `CMMeterFill ${ColourBackPre}${colour}`;
  fill.style.width = `${Math.round(Math.min(Math.max(fraction, 0), 1) * 1000) / 10}%`;
  meter.appendChild(fill);
  const text = document.createElement('div');
  text.className = 'CMMeterLabel';
  text.textContent = label;
  meter.appendChild(text);
  return meter;
}

/**
 * Creates the round "?" that shows one of the simple tooltips on hover
 * @param	{string}	placeholder	The id of the tooltip in SimpleTooltipElements
 * @returns	{object}	span
 */
function CreateHelpBubble(placeholder) {
  const bubble = document.createElement('span');
  bubble.className = 'CMHelpBubble';
  bubble.textContent = '?';
  bubble.onmouseout = function () {
    Game.tooltip.hide();
  };
  bubble.onmouseover = function () {
    Game.tooltip.draw(this, escape(SimpleTooltipElements[placeholder].innerHTML));
  };
  return bubble;
}

/**
 * This function creates the "Ascension Advisor" section of the stats page
 * @returns	{object}	section		The object containing the section
 */
export default function AscensionSection() {
  const summary = AscensionSummary();

  const section = document.createElement('div');
  section.className = 'CMStatsAscensionSection CMAdvisor';

  const headline = document.createElement('div');
  headline.className = `CMAdvisorHeadline ${ColourTextPre}${summary.colour}`;
  headline.appendChild(document.createTextNode(`${summary.headline} `));
  headline.appendChild(CreateHelpBubble('AscendAdvisorTooltipPlaceholder'));
  section.appendChild(headline);
  if (summary.status === 'na' || summary.status === 'early') return section;

  if (summary.status !== 'none') {
    section.appendChild(
      CreateMeter(
        summary.readiness,
        summary.colour,
        summary.status === 'ready'
          ? 'Optimal point reached'
          : `${FormatPercent(summary.readiness * 100)} of the optimal run completed`,
      ),
    );
  }

  const grid = document.createElement('div');
  grid.className = 'CMAdvisorGrid';
  const row = (label, value) => {
    const name = document.createElement('div');
    name.className = 'CMAdvisorLabel';
    name.textContent = label;
    grid.appendChild(name);
    const content = document.createElement('div');
    content.textContent = value;
    grid.appendChild(content);
  };
  row(
    'Ascending now',
    `+${Beautify(summary.levelsNow)} prestige level${summary.levelsNow === 1 ? '' : 's'}, +${FormatPercent(
      summary.speedGainNow * 100,
    )} production in every future run`,
  );
  if (summary.status === 'wait') {
    row(
      'At the optimum',
      `+${Beautify(summary.levelsAtTarget)} prestige levels, +${FormatPercent(
        summary.speedGainAtTarget * 100,
      )} production`,
    );
    if (summary.costOfAscendingNow !== null)
      row(
        'Ascending early costs',
        `≈ ${ShortDuration(summary.costOfAscendingNow)} of total progress`,
      );
  }
  row('This run', `${ShortDuration(summary.runTime)} long, cookies baked growing like time`);
  const exponent = document.createElement('sup');
  exponent.textContent = summary.beta.toFixed(1);
  grid.lastChild.appendChild(exponent);
  section.appendChild(grid);

  const checklist = [];
  if (CacheWrinklersTotal > 0)
    checklist.push(
      `Pop all wrinklers before ascending (+${Beautify(CacheWrinklersTotal)} cookies)`,
    );
  if (Game.HasUnlocked('Chocolate egg') && !Game.Has('Chocolate egg'))
    checklist.push(
      `Buy the Chocolate egg right before ascending (+${Beautify(CacheLastChoEgg)} cookies)`,
    );
  // Heavenly chips: what ascending now would buy along the purchase order, and what comes next
  const order = AscensionCache.heavenlyOrder;
  let chips = Game.heavenlyChips + Math.max(0, summary.levelsNow);
  const buys = [];
  if (!Game.Upgrades.Legacy.bought && chips >= 1) {
    buys.push('Legacy');
    chips -= 1;
  }
  let index = 0;
  while (index < order.length && order[index].cost <= chips) {
    buys.push(order[index].name);
    chips -= order[index].cost;
    index += 1;
  }
  if (buys.length > 0)
    checklist.push(
      `Ascending now buys ${buys.slice(0, 4).join(', ')}${
        buys.length > 4 ? ` and ${buys.length - 4} more` : ''
      } with heavenly chips`,
    );
  if (index < order.length)
    checklist.push(
      `Next heavenly upgrade: ${order[index].name} (${Beautify(order[index].cost)} chips${
        order[index].bundle.length > 1 ? ' with its parents' : ''
      }, +${FormatPercent((order[index].mult - 1) * 100)} production)`,
    );
  if (checklist.length > 0) {
    const list = document.createElement('ul');
    list.className = 'CMChecklist';
    checklist.forEach((item) => {
      const li = document.createElement('li');
      li.textContent = item;
      list.appendChild(li);
    });
    section.appendChild(list);
  }
  return section;
}

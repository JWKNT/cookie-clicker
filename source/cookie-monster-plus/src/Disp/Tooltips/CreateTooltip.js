import {
  ColourTextPre,
  ColourBorderPre,
  ColourGray,
  ColourBlue,
  ColourRed,
  ColourYellow,
  ColourPurple,
  TooltipType,
} from '../VariablesAndData.js';

/** Creates various sections of tooltips */

/**
 * This function creates a tooltipBox object which contains all CookieMonster added tooltip information.
 * @returns {object}	div		An object containing the stylized box
 */
export function TooltipCreateTooltipBox() {
  l('tooltip').firstChild.style.paddingBottom = '4px'; // Sets padding on base-tooltip
  const tooltipBox = document.createElement('div');
  tooltipBox.style.border = '1px solid';
  tooltipBox.style.padding = '4px';
  tooltipBox.style.margin = '0px -4px';
  tooltipBox.id = 'CMTooltipBorder';
  tooltipBox.className = ColourTextPre + ColourGray;
  return tooltipBox;
}

/**
 * This function creates a header object for tooltips.
 * @param	{string}	text	Title of header, also used for its id
 * @param	{string}	[label]	Text to display instead of the title
 * @returns {object}	div		An object containing the stylized header
 */
export function TooltipCreateHeader(text, label) {
  const div = document.createElement('div');
  div.style.fontWeight = 'bold';
  div.id = `${text}Title`;
  div.className = ColourTextPre + ColourBlue;
  div.textContent = typeof label === 'undefined' ? text : label;
  return div;
}

/**
 * This function creates the tooltip object for warnings: one box with a row per bank threshold
 * The object is also removed by CM.Disp.UpdateTooltipWarnings() when type is 's' or 'g'
 * @returns {object}	TooltipWarn	The Warnings-tooltip object
 */
export function TooltipCreateWarningSection() {
  const TooltipWarn = document.createElement('div');
  TooltipWarn.style.position = 'absolute';
  TooltipWarn.style.display = 'block';
  TooltipWarn.style.left = 'auto';
  TooltipWarn.style.bottom = 'auto';
  TooltipWarn.id = 'CMDispTooltipWarningParent';

  const box = document.createElement('div');
  box.id = 'CMDispTooltipWarnBox';
  box.className = `CMWarnBox ${ColourBorderPre}${ColourRed}`;
  box.style.display = 'none';
  const title = document.createElement('div');
  title.className = `CMWarnTitle ${ColourTextPre}${ColourRed}`;
  title.textContent = 'Buying this drops your bank below:';
  box.appendChild(title);

  const create = function (rowId, colour, label, deficitId, tooltip) {
    const row = document.createElement('div');
    row.id = rowId;
    row.className = 'CMWarnRow';
    row.style.display = 'none';
    row.title = tooltip;
    const labelSpan = document.createElement('span');
    labelSpan.className = ColourTextPre + colour;
    labelSpan.textContent = label;
    row.appendChild(labelSpan);
    const deficitSpan = document.createElement('span');
    deficitSpan.id = deficitId;
    row.appendChild(deficitSpan);
    return row;
  };

  box.appendChild(
    create(
      'CMDispTooltipWarnLucky',
      ColourRed,
      '"Lucky!"',
      'CMDispTooltipWarnLuckyText',
      'Bank needed for a maximum "Lucky!" reward',
    ),
  );
  box.appendChild(
    create(
      'CMDispTooltipWarnLuckyFrenzy',
      ColourYellow,
      '"Lucky!" (Frenzy)',
      'CMDispTooltipWarnLuckyFrenzyText',
      'Bank needed for a maximum "Lucky!" reward during a Frenzy',
    ),
  );
  box.appendChild(
    create(
      'CMDispTooltipWarnConjure',
      ColourPurple,
      'Conjure Baked Goods',
      'CMDispTooltipWarnConjureText',
      'Bank needed for a maximum "Conjure Baked Goods" reward',
    ),
  );
  box.appendChild(
    create(
      'CMDispTooltipWarnConjureFrenzy',
      ColourPurple,
      'Conjure (Frenzy)',
      'CMDispTooltipWarnConjureFrenzyText',
      'Bank needed for a maximum "Conjure Baked Goods" reward during a Frenzy',
    ),
  );
  box.appendChild(
    create(
      'CMDispTooltipWarnEdifice',
      ColourPurple,
      'Spontaneous Edifice',
      'CMDispTooltipWarnEdificeText',
      'Bank needed for "Spontaneous Edifice" to possibly give you your most expensive building',
    ),
  );
  box.appendChild(
    create(
      'CMDispTooltipWarnUser',
      ColourRed,
      `${Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod.settings.ToolWarnUser}s of CPS`,
      'CMDispTooltipWarnUserText',
      'Custom warning set in the Cookie Monster settings',
    ),
  );
  TooltipWarn.appendChild(box);

  return TooltipWarn;
}

/**
 * This function appends the sections for Bonus Income, PP and Time left (to achiev) to the tooltip-object
 * They are laid out as a two-column grid of label and value; the actual data is added by the Update-functions
 * @param	{object}	tooltip		Object of a TooltipBox, normally created by a call to CM.Disp.TooltipCreateTooltipBox()
 */
export function TooltipCreateCalculationSection(tooltip) {
  const grid = document.createElement('div');
  grid.className = 'CMTooltipGrid';
  grid.id = 'CMTooltipGrid';
  const add = function (title, label, valueId, hidden) {
    const header = TooltipCreateHeader(title, label);
    header.classList.add('CMTooltipLabel');
    const value = document.createElement('div');
    value.id = valueId;
    value.className = 'CMTooltipValue';
    if (hidden) {
      header.style.display = 'none';
      value.style.display = 'none';
    }
    grid.appendChild(header);
    grid.appendChild(value);
    return header;
  };

  add('Bonus Income', 'Bonus income', 'CMTooltipIncome');
  add('Bonus Cookies per Click', 'Bonus per click', 'CMTooltipCookiePerClick', true);
  add('Payback Period', 'Payback period', 'CMTooltipPP');
  add('Time Left', 'Time left', 'CMTooltipTime');
  if (TooltipType === 'b') {
    add(
      'Production left till next achievement',
      'Output achiev. in',
      'CMTooltipProductionLeft',
      true,
    ).id = 'CMTooltipProductionLeftHeader';
    add(
      'Buildings (price / PP) left till next achievement',
      'Count achiev. in',
      'CMTooltipNextAchievement',
      true,
    ).id = 'CMTooltipNextAchievementHeader';
  }
  tooltip.appendChild(grid);
}

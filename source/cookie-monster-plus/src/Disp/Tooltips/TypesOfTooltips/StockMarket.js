import Beautify from '../../BeautifyAndFormatting/Beautify.js';
import {
  TooltipName,
  ColourTextPre,
  ColourGreen,
  ColourYellow,
  ColourOrange,
  ColourRed,
  ColourPurple,
  ColourGray,
} from '../../VariablesAndData.js';
import CalculateStockNextExpectedValue from '../../HelperFunctions/CalculateStockNextExpectedValue.js';
import * as Create from '../CreateTooltip.js';

/**
 * This function adds extra info to the stock market
 * It adds to the additional information to l('CMTooltipArea')
 */
export default function StockMarket() {
  const { minigame } = Game.Objects.Bank;
  if (Game.mods.cookieMonsterFramework.saveData.cookieMonsterMod.settings.TooltipStocks) {
    const tooltipBox = l('CMTooltipBorder');
    const stock = minigame.goodsById[TooltipName];

    // Current stock mode
    tooltipBox.appendChild(Create.TooltipCreateHeader('Current Mode'));
    const stockMode = document.createElement('div');
    stockMode.id = 'CMTooltipMode';
    tooltipBox.appendChild(stockMode);
    const modeIndex = stock.mode;
    const modes = ['Stable', 'Slow Rise', 'Slow Fall', 'Fast Rise', 'Fast Fall', 'Chaotic'];
    stockMode.textContent = modes[modeIndex];
    const colours = [ColourGray, ColourYellow, ColourOrange, ColourGreen, ColourRed, ColourPurple];
    stockMode.className = ColourTextPre + colours[modeIndex];

    // Current stock delta value
    tooltipBox.appendChild(Create.TooltipCreateHeader('Delta'));
    const delta = document.createElement('div');
    delta.id = 'CMTooltipDelta';
    tooltipBox.appendChild(delta);
    delta.textContent = Beautify(stock.d);
    const deltaColour = stock.d < 0 ? ColourRed : ColourGreen;
    delta.className = ColourTextPre + deltaColour;

    // Stock resting value
    tooltipBox.appendChild(Create.TooltipCreateHeader('Resting Value'));
    const restingValue = document.createElement('div');
    restingValue.id = 'CMTooltipRestingValue';
    tooltipBox.appendChild(restingValue);
    restingValue.textContent = `$${Beautify(minigame.getRestingVal(stock.id))}`;
    restingValue.style.color = 'white';

    // Next expected value
    tooltipBox.appendChild(Create.TooltipCreateHeader('Expected Next Value'));
    const expectedNextValue = document.createElement('div');
    expectedNextValue.id = 'CMTooltipExpectedValue';
    tooltipBox.appendChild(expectedNextValue);
    const expectedValue = CalculateStockNextExpectedValue(
      stock.val,
      stock.d,
      minigame.getRestingVal(stock.id),
      stock.mode,
      Game.Objects.Bank.level,
      Game.auraMult('Supreme Intellect'),
    );
    expectedNextValue.textContent = `$${
      Beautify(expectedValue) + (expectedValue < stock.val ? '\u25bc' : '\u25b2')
    }`;
    const expectedNextValueColour = expectedValue < stock.val ? ColourRed : ColourGreen;
    expectedNextValue.className = ColourTextPre + expectedNextValueColour;

    l('CMTooltipArea').appendChild(tooltipBox);
  } else l('CMTooltipArea').style.display = 'none';
}

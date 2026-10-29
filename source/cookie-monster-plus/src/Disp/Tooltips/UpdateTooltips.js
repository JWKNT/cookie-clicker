import CopyData from '../../Sim/SimulationData/CopyData.js';
import { TooltipName, TooltipType } from '../VariablesAndData.js';
import * as Create from './CreateTooltip.js';
import Building from './TypesOfTooltips/Building.js';
import GardenPlots from './TypesOfTooltips/GardenPlots.js';
import StockMarket from './TypesOfTooltips/StockMarket.js';
import Grimoire from './TypesOfTooltips/Grimoire.js';
import HarvestAll from './TypesOfTooltips/HarvestAll.js';
import PantheonGods from './TypesOfTooltips/PantheonGods.js';
import SugarLump from './TypesOfTooltips/SugarLump.js';
import Upgrade from './TypesOfTooltips/Upgrade.js';
import Warnings from './TypesOfTooltips/Warnings.js';
import WrinklerButton from './TypesOfTooltips/WrinklerButton.js';

/**
 * This function updates the sections of the tooltips created by CookieMonster
 */
export default function UpdateTooltips() {
  CopyData();
  if (l('tooltipAnchor').style.display !== 'none' && l('CMTooltipArea')) {
    l('CMTooltipArea').innerHTML = '';
    const tooltipBox = Create.TooltipCreateTooltipBox();
    l('CMTooltipArea').appendChild(tooltipBox);

    if (TooltipType === 'b') {
      Building();
    } else if (TooltipType === 'u') {
      Upgrade();
    } else if (TooltipType === 's') {
      SugarLump();
    } else if (TooltipType === 'g') {
      Grimoire();
    } else if (TooltipType === 'p') {
      GardenPlots();
    } else if (TooltipType === 'ha') {
      HarvestAll();
    } else if (TooltipType === 'sm') {
      StockMarket();
    } else if (TooltipType === 'wb') {
      WrinklerButton();
    } else if (TooltipType === 'pag' || (TooltipType === 'pas' && TooltipName[1] !== -1)) {
      PantheonGods();
    }
    Warnings();
  } else if (l('CMTooltipArea') === null) {
    // Remove warnings if its a basic tooltip
    if (l('CMDispTooltipWarningParent') !== null) {
      l('CMDispTooltipWarningParent').remove();
    }
  }
}

import { CacheWrinklersFattest, CacheWrinklersNormal } from '../../../Cache/VariablesAndData.js';
import Beautify from '../../BeautifyAndFormatting/Beautify.js';
import { TooltipName } from '../../VariablesAndData.js';
import * as Create from '../CreateTooltip.js';

/**
 * This function adds extra info to the wrinkler button tooltip
 * It adds to the additional information to l('CMTooltipArea')
 */
export default function WrinklerButton() {
  l('tooltip').innerHTML = '';
  l('tooltip').appendChild(Create.TooltipCreateHeader('Reward:'));

  const WrinklerReward = document.createElement('div');
  WrinklerReward.id = 'CMWrinklerReward';
  if (TooltipName === 'PopAllNormal') {
    WrinklerReward.textContent = Beautify(CacheWrinklersNormal);
  } else if (TooltipName === 'PopFattest') {
    WrinklerReward.textContent = Beautify(CacheWrinklersFattest[0]);
  }

  l('tooltip').appendChild(WrinklerReward);
}

import InitCache from '../Cache/CacheInit.js';
import { CacheStatsCookies } from '../Cache/Stats/Stats.js';
import { VersionMajor, VersionMinor } from '../Data/Moddata.js';
import CreateUpgradeBar from '../Disp/BuildingsUpgrades/UpgradeBar.js';
import { CreateBotBar } from '../Disp/InfoBars/BottomBar.js';
import { CreateTimerBar } from '../Disp/InfoBars/TimerBar.js';
import CreateSectionHideButtons from '../Disp/Initialization/CreateSectionHideButtons.js';
import CreateWrinklerButtons from '../Disp/Initialization/CreateWrinklerButton.js';
import CreateCssArea from '../Disp/Initialization/CssArea.js';
import UpdateBuildingUpgradeStyle from '../Disp/Initialization/UpdateBuildingUpgradeStyle.js';
import { CreateFavicon } from '../Disp/TabTitle/FavIcon.js';
import { CreateSimpleTooltip } from '../Disp/Tooltips/Tooltip.js';
import { CMLastAscendState, TooltipText } from '../Disp/VariablesAndData.js'; // eslint-disable-line no-unused-vars
import InitData from '../Sim/InitializeData/InitData.js';
import ReplaceNativeGrimoire from './ReplaceGameElements/NativeGrimoire.js';
import ReplaceTooltips from './ReplaceGameElements/Tooltips.js';
import ReplaceNative from './ReplaceGameFunctions/ReplaceNative.js';
import { LastModCount } from './VariablesAndData.js'; // eslint-disable-line no-unused-vars
import AddWrinklerAreaDetect from './WrinklerArea/AddDetectArea.js';
import createBuildingLockButtons from '../Disp/buildingTiles/createBuildingLockButtons.js';
// import createMenuInfo from '../Disp/MenuSections/createMenuInfo.js';
import createMenuOptions from '../Disp/MenuSections/createMenuOptions.js';

/**
 * Initialization loop of Cookie Monster
 */
export default function InitializeCookieMonster() {
  // Create global data object
  window.CookieMonsterData = {};

  // Register listeners in Cookie Monster Mod Framework
  // Commented because Framework is currently broken
  // Game.mods.cookieMonsterFramework.listeners.infoMenu.push(createMenuInfo);
  Game.mods.cookieMonsterFramework.listeners.optionsMenu.push(createMenuOptions);

  InitData();
  CacheStatsCookies();
  InitCache();

  // Stored to check if we need to re-initiliaze data
  LastModCount = Object.keys(Game.mods).length;

  // Creating visual elements
  CreateCssArea();
  CreateBotBar();
  CreateTimerBar();
  CreateUpgradeBar();
  CreateSectionHideButtons();
  CreateFavicon();
  Object.keys(TooltipText).forEach((i) => {
    CreateSimpleTooltip(TooltipText[i][0], TooltipText[i][1], TooltipText[i][2]);
  });
  CreateWrinklerButtons();
  UpdateBuildingUpgradeStyle();
  createBuildingLockButtons();

  ReplaceTooltips();
  AddWrinklerAreaDetect();

  // Replace native functions
  ReplaceNative();
  ReplaceNativeGrimoire();
  Game.CalculateGains();

  CMLastAscendState = Game.OnAscend;

  if (Game.prefs.popups)
    Game.Popup(`Cookie Monster version ${VersionMajor}.${VersionMinor} loaded!`);
  else Game.Notify(`Cookie Monster version ${VersionMajor}.${VersionMinor} loaded!`, '', '', 1, 1);

  Game.Win('Third-party');
}

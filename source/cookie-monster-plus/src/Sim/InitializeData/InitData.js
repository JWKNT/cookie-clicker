/** Functions used to create static objects of Buildings, Upgrades and Achievements */

import CopyData from '../SimulationData/CopyData.js';
import { SimAchievements, SimObjects, SimUpgrades } from '../VariablesAndData.js';
import InitAchievement from './InitAchievement.js';
import InitialBuildingData from './InitialBuildingData.js';
import InitUpgrade from './InitUpgrade.js';

/**
 * This function creates static objects for Buildings, Upgrades and Achievements
 */
export default function InitData() {
  // Buildings
  SimObjects = [];
  Object.keys(Game.Objects).forEach((i) => {
    SimObjects[i] = InitialBuildingData(i);
  });

  // Upgrades
  SimUpgrades = [];
  Object.keys(Game.Upgrades).forEach((i) => {
    SimUpgrades[i] = InitUpgrade(i);
  });

  // Achievements
  SimAchievements = [];
  Object.keys(Game.Achievements).forEach((i) => {
    SimAchievements[i] = InitAchievement(i);
  });
  CopyData();
}

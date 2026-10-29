import { DispCSS } from '../VariablesAndData.js';

/** Static layout rules for the advisor, meters, compact tooltips and warnings */
const LayoutCSS = `
.CMAdvisor {
  margin: 4px 16px 10px;
  padding: 8px 10px;
  border: 1px solid rgba(255, 255, 255, 0.15);
  border-radius: 6px;
  background: rgba(0, 0, 0, 0.35);
}
.CMAdvisorHeadline { font-size: 15px; font-weight: bold; margin-bottom: 6px; }
.CMAdvisorGrid {
  display: grid;
  grid-template-columns: max-content 1fr;
  gap: 2px 12px;
  margin-top: 8px;
  font-size: 12px;
}
.CMAdvisorLabel { opacity: 0.65; }
.CMChecklist { margin: 8px 0 0 16px; padding: 0; font-size: 11px; opacity: 0.9; list-style: disc; }
.CMChecklist li { margin: 1px 0; }
.CMMeter {
  position: relative;
  height: 15px;
  border-radius: 8px;
  background: rgba(255, 255, 255, 0.08);
  box-shadow: inset 0 0 0 1px rgba(0, 0, 0, 0.6);
  overflow: hidden;
}
.CMMeterFill { position: absolute; left: 0; top: 0; bottom: 0; border-radius: 8px; transition: width 0.5s ease-out; }
.CMMeterLabel {
  position: absolute;
  inset: 0;
  font-size: 11px;
  line-height: 15px;
  font-weight: bold;
  text-align: center;
  color: #fff;
  text-shadow: 0 0 2px #000, 0 0 2px #000, 0 0 2px #000;
}
.CMHelpBubble {
  display: inline-block;
  width: 12px;
  height: 12px;
  border-radius: 6px;
  background: #c0c0c0;
  color: #000;
  font-size: 10px;
  line-height: 12px;
  text-align: center;
  vertical-align: middle;
  cursor: default;
}
.CMTooltipGrid {
  display: grid;
  grid-template-columns: max-content 1fr;
  gap: 1px 8px;
  align-items: baseline;
}
.CMTooltipGrid > .CMTooltipLabel { font-weight: bold; white-space: nowrap; }
.CMTooltipGrid > .CMTooltipValue { color: #fff; }
.CMTooltipNote { margin-top: 3px; font-size: 10px; opacity: 0.75; }
#CMDispTooltipWarningParent .CMWarnBox {
  padding: 3px 6px 4px;
  background: #000 url(img/darkNoise.png);
  border-radius: 3px;
}
#CMDispTooltipWarningParent .CMWarnTitle { font-weight: bold; margin-bottom: 2px; }
#CMDispTooltipWarningParent .CMWarnRow {
  display: flex;
  justify-content: space-between;
  gap: 10px;
  font-size: 11px;
  line-height: 14px;
}
#CMDispTooltipWarningParent .CMWarnRow > span:first-child { font-weight: bold; white-space: nowrap; }
#CMDispTooltipWarningParent .CMWarnRow > span:last-child { text-align: right; }
`;

/**
 * This function creates a CSS style that stores certain standard CSS classes used by CookieMonster
 * The colour classes are (re)written by UpdateColours(), the layout classes are static
 */
export default function CreateCssArea() {
  DispCSS = document.createElement('style');
  DispCSS.type = 'text/css';
  DispCSS.id = 'CMCSS';

  document.head.appendChild(DispCSS);

  const layout = document.createElement('style');
  layout.type = 'text/css';
  layout.id = 'CMLayoutCSS';
  layout.textContent = LayoutCSS;
  document.head.appendChild(layout);
}

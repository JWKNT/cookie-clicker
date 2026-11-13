import { writeFileSync } from 'node:fs';
import { runNativeBrowser } from '../model/native-browser.mjs';

const report = runNativeBrowser(`()=>({
  navigator:{userAgent:navigator.userAgent,appVersion:navigator.appVersion,platform:navigator.platform,
    language:navigator.language,languages:Array.from(navigator.languages)},
  screen:{width:screen.width,height:screen.height,availWidth:screen.availWidth,availHeight:screen.availHeight,
    colorDepth:screen.colorDepth,pixelDepth:screen.pixelDepth},
  window:{devicePixelRatio,innerWidth,innerHeight,outerWidth,outerHeight},
  document:{URL:document.URL,compatMode:document.compatMode,characterSet:document.characterSet},
  location:{href:location.href,protocol:location.protocol,origin:location.origin,
    host:location.host,hostname:location.hostname,port:location.port,pathname:location.pathname,
    search:location.search,hash:location.hash}
})`, null, { documentMode: 'file' });
const output = {
  schema: 1,
  interpretation: 'Explicit fixture configuration observed in the isolated audit document. These values are not universal browser laws or a claim that the game uses this document URL or window size.',
  versions: report.versions, architecture: report.identity.arch, platform: report.identity.platform,
  executableSha256: report.executableHash, auditConfiguration: report.auditConfiguration,
  gameEntryPointExecuted: report.gameEntryPointExecuted, externalNetworking: report.externalNetworking,
  configuration: report.result,
};
writeFileSync(new URL('../model/browser-fixture-config.json', import.meta.url), JSON.stringify(output, null, 2) + '\n');
console.log(JSON.stringify({ navigator: output.configuration.navigator, screen: output.configuration.screen, window: output.configuration.window }));

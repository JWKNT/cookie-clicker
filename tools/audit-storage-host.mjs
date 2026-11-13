import { readFileSync, writeFileSync } from 'node:fs';
import { createHash } from 'node:crypto';
import { runNativeBrowser } from '../model/native-browser.mjs';

const files = [
  ['electron-dom-storage-limits.patch','https://raw.githubusercontent.com/electron/electron/v11.5.0/patches/chromium/dom_storage_limits.patch'],
  ['cached_storage_area.cc','https://raw.githubusercontent.com/chromium/chromium/87.0.4280.141/third_party/blink/renderer/modules/storage/cached_storage_area.cc'],
  ['storage_area_map.cc','https://raw.githubusercontent.com/chromium/chromium/87.0.4280.141/third_party/blink/renderer/modules/storage/storage_area_map.cc'],
];
const sources=files.map(([file,url])=>({file,url,sha256:createHash('sha256')
  .update(readFileSync(new URL('../model/browser-source/chromium-87/'+file,import.meta.url))).digest('hex')}));
const report=runNativeBrowser(`()=>{
 const quota=104857600, units=quota/2, results=[];
 for(const area of ['localStorage','sessionStorage']){
   const s=window[area];s.clear();let oversized;
   try{s.setItem('', 'x'.repeat(units+1));oversized='accepted';}catch(e){oversized=e.name;}
   const afterFailure=s.length;
   s.setItem('', 'x'.repeat(units));
   let addedKey;try{s.setItem('x','');addedKey='accepted';}catch(e){addedKey=e.name;}
   const atBoundary=s.getItem('').length;
   s.setItem('', 'x'.repeat(units-1));s.setItem('x','');
   results.push({area,oversized,afterFailure,addedKey,atBoundary,afterShrink:s.length});s.clear();
 }
 return results;
}`,null,{documentMode:'file',timeout:120000});
for(const x of report.result){
 if(x.oversized!=='QuotaExceededError'||x.addedKey!=='QuotaExceededError'||x.afterFailure!==0||
    x.atBoundary!==52428800||x.afterShrink!==2)throw new Error('Native quota boundary mismatch: '+JSON.stringify(x));
}
const witness={schema:1,scope:'isolated-native-Storage-quota-boundaries-not-full-host-refinement',
  quotaBytes:104857600,unit:'two bytes per UTF-16 code unit in keys and values',sources,
  executableSha256:report.executableHash,versions:report.versions,auditConfiguration:report.auditConfiguration,
  gameEntryPointExecuted:report.gameEntryPointExecuted,externalNetworking:report.externalNetworking,
  cases:report.result,remaining:['Native multiple-key iteration order','Exotic named-property reflection',
    'Cross-window storage events and backend failures','Full source/host refinement']};
writeFileSync(new URL('../model/storage-host-witness.json',import.meta.url),JSON.stringify(witness,null,2)+'\n');
console.log(JSON.stringify({quotaBytes:witness.quotaBytes,areas:report.result.length,boundaryChecks:12}));

import {writeFileSync} from 'node:fs';
import {createHash} from 'node:crypto';
import {runNativeBrowser} from '../model/native-browser.mjs';

const report=runNativeBrowser(function(){
  return Object.getOwnPropertyNames(document.createElement('div').style).map(javascriptName=>{
    const style=document.createElement('div').style;
    style[javascriptName]='initial';
    if(style[javascriptName]!=='initial') {
      if(style[javascriptName]!=='' || style.cssText!=='') throw Error('Unexpected empty-style member '+javascriptName);
      // Native font-face-only descriptors are exposed as JS names, but an
      // inline declaration does not accept this declaration value.
      return {javascriptName,cssName:null,aliases:[],longhands:[],initialAccepted:false};
    }
    const cssName=style.cssText.slice(0,style.cssText.indexOf(':'));
    if(style.cssText==='') return {javascriptName,cssName:null,aliases:[],longhands:[],initialAccepted:false,assignedValue:style[javascriptName]};
    if(!cssName || style.getPropertyValue(cssName)!=='initial') throw Error('No canonical CSS name for '+javascriptName);
    const derived=javascriptName==='cssFloat'?'float':javascriptName.replace(/[A-Z]/g,c=>'-'+c.toLowerCase());
    const candidates=[cssName,derived,derived.startsWith('webkit-')?'-'+derived:derived];
    const aliases=candidates.filter((value,index)=>candidates.indexOf(value)===index && style.getPropertyValue(value)==='initial');
    const longhands=Array.from({length:style.length},(_,index)=>style.item(index));
    return {javascriptName,cssName,aliases,longhands,initialAccepted:true};
  });
}.toString(),null,{allowInlineStyles:true});
const reportData={schema:1,scope:'native-CSS-name-and-expansion-table-not-value-parser-or-renderer',
  versions:report.versions,executableSha256:report.executableHash,
  gameEntryPointExecuted:report.gameEntryPointExecuted,externalNetworking:report.externalNetworking,
  inspection:'Each own property of a detached empty CSS declaration is assigned the CSS-wide keyword initial. The canonical serialized name, accepted aliases and longhand property names are recorded.',
  properties:report.result,
  propertiesSha256:createHash('sha256').update(JSON.stringify(report.result)).digest('hex')};
writeFileSync(new URL('../model/css-properties.json',import.meta.url),JSON.stringify(reportData,null,2)+'\n');
console.log(JSON.stringify({properties:report.result.length,propertiesSha256:reportData.propertiesSha256}));

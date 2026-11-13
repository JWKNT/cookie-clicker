/** Storage host comparisons. Fresh isolated profiles; no real save access. */
import assert from 'node:assert/strict';
import { spawnSyncWithFileInput as spawnSync } from './process-input.mjs';
import { fileURLToPath } from 'node:url';
import { compileJavaScript } from '../model/javascript-ast.mjs';
import { loadGameSource } from '../model/game-source.mjs';
import { runNativeBrowser } from '../model/native-browser.mjs';

const cases=[];
const add=(name,source,extra={})=>cases.push({name,source,origin:'enabled',quotaBytes:104857600,...extra});
add('same native storage identities and separate areas',
  '(localStorage===window.localStorage)+":"+(sessionStorage===window.sessionStorage)+":"+(localStorage!==sessionStorage)+":"+(localStorage instanceof Storage);');
add('replacing the global constructor preserves intrinsic storage prototypes',
  'var saved=Storage;Storage=function Replacement(){};var out=(localStorage instanceof saved)+":"+(sessionStorage instanceof saved)+":"+(localStorage instanceof Storage);Storage=saved;out;');
add('empty storage and absent item','localStorage.length+":"+localStorage.getItem("none")+":"+localStorage.key(0);');
add('setItem returns undefined and replaces without a second key','var a=localStorage.setItem("a","one"),b=localStorage.setItem("a","two");a+":"+b+":"+localStorage.length+":"+localStorage.getItem("a");');
add('local and session values are separate','localStorage.setItem("a","local");sessionStorage.setItem("a","session");localStorage.getItem("a")+":"+sessionStorage.getItem("a");');
add('primitive key and value string conversion','localStorage.setItem(null,undefined);localStorage.setItem(false,true);localStorage.getItem("null")+":"+localStorage.getItem(false);');
add('source key converts before source value','var log="";localStorage.setItem({toString:function(){log+="k";return "a";}},{toString:function(){log+="v";return "b";}});log+":"+localStorage.getItem("a");');
add('source key throw skips value conversion','var log="";try{localStorage.setItem({toString:function(){log+="k";throw 3;}},{toString:function(){log+="v";return "b";}});}catch(e){log+=e;}log+":"+localStorage.length;');
add('missing value is rejected before key conversion','var log="";try{localStorage.setItem({toString:function(){log+="k";return "a";}});}catch(e){log+=e.name;}log;');
add('receiver checked before argument conversion','var log="";try{Storage.prototype.setItem.call({}, {toString:function(){log+="k";return "a";}},"v");}catch(e){log+=e.name;}log;');
add('methods do not accept null receiver','try{Storage.prototype.getItem.call(null,"a");}catch(e){e.name;}');
add('getItem source string conversion','localStorage.setItem("a","b");var log="";var v=localStorage.getItem({toString:function(){log+="k";return "a";}});log+":"+v;');
add('removeItem does not add an absent key','localStorage.setItem("a","b");var x=localStorage.removeItem("none");var y=localStorage.removeItem("a");x+":"+y+":"+localStorage.length+":"+localStorage.getItem("a");');
add('clear ignores extra arguments','localStorage.setItem("a","b");var x=localStorage.clear({toString:function(){throw 3;}});x+":"+localStorage.length;');
add('empty string key and value remain entries','localStorage.setItem("","");localStorage.length+":"+(localStorage.getItem("")==="")+":"+(localStorage.key(0)==="");');
add('single key index uses unsigned32 conversion','localStorage.setItem("a","b");localStorage.key(4294967296)+":"+localStorage.key(-1)+":"+localStorage.key(NaN)+":"+localStorage.key(Infinity);');
add('key conversion invokes source valueOf','localStorage.setItem("a","b");var log="";var k=localStorage.key({valueOf:function(){log+="v";return 0;}});log+":"+k;');
add('required argument failures','var out="";try{localStorage.getItem();}catch(e){out+=e.name;}try{localStorage.removeItem();}catch(e){out+=":"+e.name;}try{localStorage.key();}catch(e){out+=":"+e.name;}out;');
add('storage strings retain nonBMP and unpaired units','localStorage.setItem("\ud800\ud83d\ude00","\udfff\u0000x");localStorage.getItem("\ud800\ud83d\ude00");');
add('prototype names remain valid stored keys','localStorage.setItem("getItem","x");localStorage.setItem("length","y");localStorage.setItem("__proto__","z");typeof localStorage.getItem+":"+localStorage.length+":"+localStorage.getItem("getItem")+":"+localStorage.getItem("length")+":"+localStorage.getItem("__proto__");');
add('ordinary named reads and membership','localStorage.setItem("sourceKey","v");localStorage.sourceKey+":"+("sourceKey" in localStorage)+":"+("absentKey" in localStorage);');
add('native Storage descriptor resumes HasProperty before Get','localStorage.setItem("value","source-value");localStorage.setItem("enumerable","");var o={};Object.defineProperty(o,"x",localStorage);var d=Object.getOwnPropertyDescriptor(o,"x");d.value+":"+d.enumerable+":"+d.writable+":"+d.configurable;');
add('inherited Storage descriptor retains field query order','localStorage.setItem("value","inherited-value");localStorage.setItem("writable","yes");var d=Object.create(localStorage),o={};Object.defineProperty(d,"enumerable",{value:true});Object.defineProperty(o,"x",d);var p=Object.getOwnPropertyDescriptor(o,"x");p.value+":"+p.enumerable+":"+p.writable+":"+p.configurable;');
add('unknown inherited host write cannot become a successful read','var d=Object.create(localStorage);d.enumerable=true;d.enumerable;',{expectedStatus:'unresolved'});
add('Storage descriptor validates stored noncallable getter','localStorage.setItem("get","invalid-getter");try{Object.defineProperty({},"x",localStorage);}catch(e){e.name;}');
add('borrowed length getter uses native branding','var get=Object.getOwnPropertyDescriptor(Storage.prototype,"length").get;var a=get.call(localStorage);try{get.call({});}catch(e){a+=":"+e.name;}a+"";');
add('Window storage getter accepts null as global','var get=Object.getOwnPropertyDescriptor(window,"localStorage").get;(get.call(null)===localStorage)+":"+(get.call(undefined)===localStorage);');
add('Window storage getter rejects unrelated receiver','var get=Object.getOwnPropertyDescriptor(window,"localStorage").get;try{get.call({});}catch(e){e.name;}');
add('opaque origin reports native SecurityError','try{window.localStorage;}catch(e){e.name;}',{origin:'denied'});
add('unconfigured origin is not treated as native denial','window.localStorage;',{origin:'unconfigured',expectedStatus:'unresolved'});
add('unconfigured quota does not allow a guessed write','localStorage.setItem("k","v");',{quotaBytes:undefined,expectedStatus:'unresolved'});
add('multi-key native iteration order remains explicit','localStorage.setItem("a","b");localStorage.setItem("c","d");localStorage.key(0);',{expectedStatus:'unresolved'});
add('configured tiny quota accepts exact bound','localStorage.setItem("a","b");localStorage.getItem("a");',{quotaBytes:4,expectedString:'b'});
add('quota failure preserves existing value','localStorage.setItem("a","b");var s="";try{localStorage.setItem("a","bc");}catch(e){s=e.name;}s+":"+localStorage.getItem("a");',{quotaBytes:4,expectedString:'QuotaExceededError:b'});
add('removal releases quota','localStorage.setItem("a","b");localStorage.removeItem("a");localStorage.setItem("c","d");localStorage.getItem("c");',{quotaBytes:4,expectedString:'d'});
const source=loadGameSource().sources['main.js'];
const from=source.indexOf('localStorageGet=function(key)'),to=source.indexOf('var ajax=function',from);
assert(from>=0&&to>from);
const wrappers=source.slice(from,to);
add('exact source wrappers preserve successful get and set',wrappers+'var a=localStorageSet("audit-key","value");a+":"+localStorageGet("audit-key")+":"+localStorageGet("missing");');
add('exact source wrappers catch opaque origin failures',wrappers+'localStorageSet("audit-key","value")+":"+localStorageGet("audit-key");',{origin:'denied'});

const requests=cases.map(c=>({ast:compileJavaScript(c.source,{name:c.name}),fuel:500000,browserLibrary:true,
  fixtureStorage:{origin:c.origin,...(c.quotaBytes===undefined?{}:{quotaBytes:c.quotaBytes})}}));
const child=spawnSync(fileURLToPath(new URL('.lake/build/bin/jsastcheck',import.meta.url)),['--execute'],{
  input:JSON.stringify(requests),encoding:'utf8',timeout:120000,maxBuffer:8*1024*1024,
});
if(child.error)throw child.error;assert.equal(child.status,0,child.stderr);const actual=JSON.parse(child.stdout);
const units=s=>Array.from({length:s.length},(_,i)=>s.charCodeAt(i));
const expected=new Map();
for(const origin of ['enabled','denied']){
  const selected=cases.filter(c=>c.origin===origin&&!c.expectedStatus&&c.expectedString===undefined);
  const report=runNativeBrowser(`cases=>cases.map(c=>{
    if(c.origin==='enabled'){localStorage.clear();sessionStorage.clear();}
    const value=(function(source){return eval(source);})(c.source);
    if(typeof value!=='string')throw new Error(c.name+' did not return a string');
    return {name:c.name,units:Array.from({length:value.length},(_,i)=>value.charCodeAt(i))};
  })`,selected,{documentMode:origin==='enabled'?'file':'data',allowEval:true});
  for(const result of report.result)expected.set(result.name,result.units);
}
for(let i=0;i<cases.length;i++){
  const c=cases[i];
  if(c.expectedStatus)assert.equal(actual[i].status,c.expectedStatus,c.name+': '+JSON.stringify(actual[i]));
  else{
    assert.equal(actual[i].status,'complete',c.name+': '+JSON.stringify(actual[i]));
    assert.deepEqual(actual[i].value,{type:'string',units:c.expectedString===undefined?expected.get(c.name):units(c.expectedString)},c.name);
  }
}
console.log(JSON.stringify({storageCases:cases.length,nativeComparisons:expected.size,explicitQuotaFixtureCases:3,
  fileOriginQuotaBytes:104857600,fullStorageHostRefinement:false}));

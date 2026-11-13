/** Native cookie accessor checks on isolated fresh file and opaque origins. */
import assert from 'node:assert/strict';
import { spawnSyncWithFileInput as spawnSync } from './process-input.mjs';
import { fileURLToPath } from 'node:url';
import { compileJavaScript } from '../model/javascript-ast.mjs';
import { runNativeBrowser } from '../model/native-browser.mjs';
if(!process.argv.includes('--engine'))throw new Error('Cookie checks require --engine with isolated native Chromium profiles');
const cases=[];
const add=(name,source,extra={})=>cases.push({name,source,...extra});
add('getter reads native origin policy','try{document.cookie;}catch(e){e.name;}');
for(const value of ['"auditCookie=one"','"auditCookie=two;path=/"','"auditCookie=three;SameSite=None;Secure"','"auditCookie=deleted;Max-Age=0"','null','undefined','17']){
  add(`setter conversion and origin policy ${value}`, `try{document.cookie=${value};document.cookie;}catch(e){e.name;}`);
}
add('setter converts source object before checking origin', 'var s="";try{document.cookie={toString:function(){s+="s";return "auditCookie=one";}};s+=":"+document.cookie;}catch(e){s+=":"+e.name;}s;');
add('source conversion throw precedes opaque-origin access error', 'var s="";try{document.cookie={toString:function(){s+="s";throw 7;}};}catch(e){s+=e;}s;');
add('object conversion preserves original assignment result', 'var o={toString:function(){return "auditCookie=one";}};try{(document.cookie=o)===o;}catch(e){e.name;}');
add('setter accepts omitted argument', 'try{Object.getOwnPropertyDescriptor(Document.prototype,"cookie").set.call(document);document.cookie;}catch(e){e.name;}');
add('getter brands receiver before native origin', 'try{Object.getOwnPropertyDescriptor(Document.prototype,"cookie").get.call({});}catch(e){e.name;}');
add('setter brands receiver before source conversion', 'var s="";try{Object.getOwnPropertyDescriptor(Document.prototype,"cookie").set.call(document.createElement("div"),{toString:function(){s+="wrong";return "a=b";}});}catch(e){s+=e.name;}s;');
add('setter primitive fallback finishes ToString', 'var s="";try{document.cookie={toString:function(){s+="s";return {};},valueOf:function(){s+="v";return null;}};s+=":"+document.cookie;}catch(e){s+=":"+e.name;}s;');
add('file writes cannot create cookies through deletion and overwrite', 'var s="";try{document.cookie="auditCookie=a";document.cookie="auditCookie=b";document.cookie="other=one";s=document.cookie;}catch(e){s=e.name;}s;');
const requests=['file','opaque'].flatMap(origin=>cases.map(c=>({ast:compileJavaScript(c.source,{name:`${origin}:${c.name}`}),browserLibrary:true,fuel:100000,fixtureCookieOrigin:origin})));
requests.push({ast:compileJavaScript('document.cookie;'),browserLibrary:true,fuel:10000});
const child=spawnSync(fileURLToPath(new URL('.lake/build/bin/jsastcheck',import.meta.url)),['--execute'],{input:JSON.stringify(requests),encoding:'utf8',timeout:60000,maxBuffer:8*1024*1024});
if(child.error)throw child.error;assert.equal(child.status,0,child.stderr);
const observed=JSON.parse(child.stdout),expected=[],runs=[];
const worker=function(cases){function encode(v){if(v===undefined)return{type:'undefined'};if(v===null)return{type:'null'};if(typeof v==='boolean')return{type:'boolean',value:v};if(typeof v==='string')return{type:'string',units:Array.from({length:v.length},(_,i)=>v.charCodeAt(i))};throw Error('Expected primitive cookie fixture result');}return cases.map(c=>({status:'complete',value:encode((function(){return eval(c.source);})())}));};
for(const documentMode of ['file','data']){const run=runNativeBrowser(worker.toString(),cases,{documentMode,allowEval:true});runs.push(run);expected.push(...run.result);}
const failures=[];
for(let i=0;i<expected.length;i++){try{assert.deepEqual({status:observed[i].status,value:observed[i].value},expected[i]);}catch(error){failures.push({origin:i<cases.length?'file':'opaque',name:cases[i%cases.length].name,observed:observed[i],expected:expected[i],error:error.message});}}
try{assert.equal(observed.at(-1).status,'unresolved');}catch(error){failures.push({name:'unconfigured origin remains explicit',observed:observed.at(-1),error:error.message});}
if(failures.length){console.error(JSON.stringify(failures,null,2));process.exitCode=1;}
console.log(JSON.stringify({cases:requests.length,passed:requests.length-failures.length,nativeComparisons:expected.length,origins:['isolated-file','isolated-data'],versions:runs[0].versions,executableHash:runs[0].executableHash,freshProfiles:true,userCookieStoreRead:false,gameEntryPointExecuted:false,javascriptSemanticsVerified:false}));

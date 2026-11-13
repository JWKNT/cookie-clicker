/** Browsing-context name state, not a heap-identity shortcut. */
import assert from 'node:assert/strict';
import {fileURLToPath} from 'node:url';
import {spawnSyncWithFileInput as spawnSync} from './process-input.mjs';
import {compileJavaScript} from '../model/javascript-ast.mjs';
import {runNativeBrowser} from '../model/native-browser.mjs';
if(!process.argv.includes('--engine'))throw new Error('Window name checks require the isolated pinned Chromium worker');
const units=s=>Array.from({length:s.length},(_,i)=>s.charCodeAt(i));
const cases=[],add=(name,source,extra={})=>cases.push({name,source,...extra});
add('explicit initial empty browsing-context name','window.name;');
add('explicit initial name survives ordinary source execution','window.name;',{initial:'target-frame'});
for(const value of ['undefined','null','true','false','0','-0','NaN','Infinity','2.053','""','"alpha\\u0000omega"','"\\ud800"','"😀"'])
  add(`DOMString setter ${value}`,`window.name=${value};window.name;`);
add('assignment returns original source object','var o={toString:function(){return "value";}};(window.name=o)===o;');
add('source string conversion uses toString before valueOf','var log="";window.name={toString:function(){log+="s";return {};},valueOf:function(){log+="v";return 3;}};log+":"+window.name;');
add('conversion throw preserves prior native name','window.name="before";try{window.name={toString:function(){throw "x";}};}catch(e){}window.name;');
add('conversion callback mutation is retained when callback throws','window.name="before";try{window.name={toString:function(){window.name="inside";throw "x";}};}catch(e){}window.name;');
add('outer completed setter follows reentrant name update','var log="";window.name={toString:function(){window.name="inside";log+=window.name;return "outer";}};log+":"+window.name;');
add('sloppy source global assignment uses actual native setter','name="big burglar";window.name;');
add('global var assignment uses the native browsing-context setter','var name=17;name+":"+window.name;');
add('source postfix update converts getter string and stores DOMString','window.name="7";var previous=window.name++;previous+":"+window.name+":"+typeof window.name;');
for(const method of ['get','set'])for(const receiver of ['undefined','null','window','{}','document']){
  add(`${method} receiver ${receiver}`,`var d=Object.getOwnPropertyDescriptor(window,"name"),log="";try{var value=d.${method}.call(${receiver},{toString:function(){log+="s";return "value";}});log+=":"+String(value)+":"+window.name;}catch(e){log+=e.name;}log;`);
}
add('omitted setter argument stores undefined string','Object.getOwnPropertyDescriptor(window,"name").set.call(window);window.name;');
add('native setter call returns undefined','Object.getOwnPropertyDescriptor(window,"name").set.call(window,"x")===undefined;');
add('native accessor cannot be constructed','var s=Object.getOwnPropertyDescriptor(window,"name").set,log="";try{new s({toString:function(){log+="wrong";return "x";}});}catch(e){log+=e.name;}log;');
add('saved getter reads native state after source property replacement','window.name="native";var d=Object.getOwnPropertyDescriptor(window,"name");Object.defineProperty(window,"name",{value:"own",configurable:true});window.name+":"+d.get.call(window);');
add('saved setter mutates native state independently of replacement property','var d=Object.getOwnPropertyDescriptor(window,"name");Object.defineProperty(window,"name",{value:"own",configurable:true});d.set.call(window,"native");window.name+":"+d.get.call(window);');
add('unconfigured initial name stays explicit','window.name;',{unconfigured:true,expectedStatus:'unresolved'});
add('setter establishes name without requiring an initial value','window.name="known";window.name;',{unconfigured:true});
const requests=cases.map(c=>({browserLibrary:true,ast:compileJavaScript(c.source,{name:c.name}),fuel:100000,...(c.unconfigured?{}:{fixtureWindowName:units(c.initial??'')})}));
const child=spawnSync(fileURLToPath(new URL('.lake/build/bin/jsastcheck',import.meta.url)),['--execute'],{input:JSON.stringify(requests),encoding:'utf8',timeout:120000,maxBuffer:8*1024*1024});
if(child.error)throw child.error;assert.equal(child.status,0,child.stderr);const observed=JSON.parse(child.stdout);
const worker=function(cases){const initialDescriptor=Object.getOwnPropertyDescriptor(window,'name');function encode(v){if(v===undefined)return{type:'undefined'};if(v===null)return{type:'null'};if(typeof v==='string')return{type:'string',units:Array.from({length:v.length},(_,i)=>v.charCodeAt(i))};if(typeof v==='boolean')return{type:'boolean',value:v};throw Error('Window fixture must return string or boolean');}return cases.map(c=>{if(c.expectedStatus)return{status:c.expectedStatus};Object.defineProperty(window,'name',initialDescriptor);window.name=c.initial??'';try{return{status:'complete',value:encode((0,eval)(c.source))};}catch(e){return{status:'throw',name:e.name,message:e.message};}finally{Object.defineProperty(window,'name',initialDescriptor);window.name='';}});};
const native=runNativeBrowser(worker.toString(),cases,{allowEval:true}),failures=[];
for(let i=0;i<cases.length;i++)try{if(cases[i].expectedStatus)assert.equal(observed[i].status,cases[i].expectedStatus);else assert.deepEqual({status:observed[i].status,value:observed[i].value},native.result[i]);}catch(error){failures.push({name:cases[i].name,observed:observed[i],expected:native.result[i],error:error.message});}
if(failures.length){console.error(JSON.stringify(failures,null,2));process.exitCode=1;}
console.log(JSON.stringify({cases:cases.length,passed:cases.length-failures.length,nativeComparisons:cases.filter(c=>!c.expectedStatus).length,versions:native.versions,executableHash:native.executableHash,gameEntryPointExecuted:false,navigationRefinementVerified:false}));

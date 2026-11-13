/** Background position storage/serialization checks; no painting refinement. */
import assert from 'node:assert/strict';
import {fileURLToPath} from 'node:url';
import {spawnSyncWithFileInput} from './process-input.mjs';
import {compileJavaScript} from '../model/javascript-ast.mjs';
import {loadGameSource} from '../model/game-source.mjs';
import {runNativeBrowser} from '../model/native-browser.mjs';
if(!process.argv.includes('--engine'))throw Error('Background position requires the isolated pinned browser');
const cases=[],add=(name,source,expectedStatus)=>cases.push({name,source,expectedStatus});
const values=['-1.5px','-.5px','.5%','-0.0px','+01.50PX','1.23456789012345px','1.23456789012345%',
 '125000.5px','125001.5px','999999.5px','1000001px','-4503599627370496px','1e100px','1e-100px',
 '1e308px','1e309px','-1e309px','5e-324px','-5e-324px','1e-400px','50.00000000001%','1.5px -2.25px',
 '-0.5px center','top .5px','center .5px','1.px','0.','1e+px','1e%','0x1px','NaNpx','Infinitypx',
 'undefined','null','.1px left','left .1px','-2.5px top'];
for(const value of values)for(const method of ['property','setProperty','attribute'])add(`${method} ${value}`,
 `var e=document.createElement('div'),s=e.style;s.backgroundPosition='7px 8px';${method==='property'?`s.backgroundPosition=${JSON.stringify(value)};`:method==='setProperty'?`s.setProperty('background-position',${JSON.stringify(value)},'important');`:`e.setAttribute('style',${JSON.stringify('background-position:'+value)});`}[s.backgroundPosition,s.backgroundPositionX,s.backgroundPositionY,s.cssText,e.getAttribute('style')].join('|');`);
for(const value of ['1.23456789012345px','125000.5px','1e100px','-1.5%'])add('precision cache survives unrelated property write '+value,
 `var e=document.createElement('div'),s=e.style;s.backgroundPosition=${JSON.stringify(value)};var a=s.backgroundPosition;s.opacity='1';s.backgroundPositionY='2.25px';[a,s.backgroundPosition,s.cssText,e.getAttribute('style')].join('|');`);
add('longhand priority prevents shorthand serialization',`var e=document.createElement('div'),s=e.style;s.setProperty('background-position-x','1.23456789012345px','important');s.backgroundPositionY='2.25px';[s.backgroundPosition,s.backgroundPositionX,s.cssText].join('|');`);
add('background URL shorthand has fractional position',`var s=document.createElement('div').style;s.background='url(img/example.png) -1.5px 2.25px';[s.background,s.backgroundPosition,s.cssText].join('|');`);
add('background transparent plus fractional position',`var s=document.createElement('div').style;s.background='transparent';s.backgroundPosition='-1.5px';[s.background,s.cssText].join('|');`);
add('source coercion preserves mutations before throw',`var s=document.createElement('div').style;try{s.backgroundPosition={toString:function(){s.backgroundPosition='-.25px';throw 'stop';}};}catch(e){}s.backgroundPosition;`);
add('source coercion returns original assignment object',`var s=document.createElement('div').style,v={toString:function(){return '-1.5px';}};(s.backgroundPosition=v)===v? s.backgroundPosition:'bad';`);
add('direct null clears but object null does not',`var s=document.createElement('div').style;s.backgroundPosition='-1.5px';s.backgroundPosition={toString:function(){return null;}};var a=s.backgroundPosition;s.backgroundPosition=null;a+'|'+s.backgroundPosition;`);
add('saved style cache invalidates after raw attribute replacement',`var e=document.createElement('div'),s=e.style;s.backgroundPosition='1.23456789012345px';e.setAttribute('style','background-position:-2.34567890123456px');s.backgroundPosition;`);
for(const value of ['calc(1px + 2px)','var(--x)','1em','1cm','left 1px top 2px','1px,2px','1px/*x*/'])add('unsupported '+value,
 `document.createElement('div').style.backgroundPosition=${JSON.stringify(value)};`,'unresolved');
const statement=loadGameSource().sources['main.js'].split('\n').find(line=>line.includes("Game.ascendMeter.style.backgroundPosition="));
assert.equal(statement.trim(),"Game.ascendMeter.style.backgroundPosition=(-Game.T*0.5-Game.ascendMeterPercent*100)+'px';");
for(const frame of [0,1,2,3,1000001,2000001,2**53])for(const percent of [0,0.00123456789012345,1])add(`actual ascendMeter source ${frame}/${percent}`,
 `var Game={ascendMeter:document.createElement('div'),T:${frame},ascendMeterPercent:${percent}};${statement}Game.ascendMeter.style.backgroundPosition;`);
const pure=['-1.5px','1.23456789012345px','125000.5px','1000001px','-4503599627370496px','1e100px','1e-100px','5e-324px','-0px','0','1.23456789012345%'];
const native=runNativeBrowser(function(input){return {cases:input.cases.map(c=>{if(c.expectedStatus)return{status:c.expectedStatus};var value=(function(){return eval(c.source);})();if(typeof value!=='string')throw Error('String result expected');return {status:'complete',value:{type:'string',units:Array.from({length:value.length},(_,i)=>value.charCodeAt(i))}};}),pure:input.pure.map(value=>{var s=document.createElement('div').style;s.backgroundPositionX=value;return s.backgroundPositionX;})};}.toString(),{cases,pure},{allowEval:true,allowInlineStyles:true});
const units=s=>Array.from({length:s.length},(_,i)=>s.charCodeAt(i));
const requests=cases.map(c=>({browserLibrary:true,fuel:100000,loadedStylesheets:[],initialHtmlUnits:units('<!doctype html><html><head></head><body></body></html>'),ast:compileJavaScript(c.source,{name:c.name})}));
const run=(target,input,args=[])=>{const r=spawnSyncWithFileInput(fileURLToPath(new URL('.lake/build/bin/'+target,import.meta.url)),args,{input:JSON.stringify(input),encoding:'utf8',timeout:120000,maxBuffer:16*1024*1024});if(r.error)throw r.error;assert.equal(r.status,0,r.stderr);return JSON.parse(r.stdout);};
const results=run('jsastcheck',requests,['--execute']),failures=[];
for(let i=0;i<cases.length;i++)try{if(cases[i].expectedStatus)assert.equal(results[i].status,cases[i].expectedStatus);else assert.deepEqual({status:results[i].status,value:results[i].value},native.result.cases[i]);}catch(error){failures.push({name:cases[i].name,observed:results[i],expected:native.result.cases[i],error:error.message});}
const internal=run('jscsscheck',pure.map(source=>({operation:'position-number',source})));
for(let i=0;i<pure.length;i++)try{const suffix=pure[i].endsWith('%')?'%':'px';const number=Math.max(-(2**128-2**104),Math.min(2**128-2**104,Number(pure[i].replace(/(?:px|%)$/,''))));assert.deepEqual(internal[i],{status:'complete',internal:String(number)+suffix,text:native.result.pure[i]});}catch(error){failures.push({name:'lossless internal position '+pure[i],observed:internal[i],error:error.message});}
if(failures.length){console.error(JSON.stringify(failures,null,2));process.exitCode=1;}
console.log(JSON.stringify({cases:cases.length,pureCases:pure.length,passed:cases.length+pure.length-failures.length,nativeComparisons:cases.filter(c=>!c.expectedStatus).length+pure.length,versions:native.versions,rendererRefinementVerified:false,internalValuesAreDiagnosticOnly:true}));

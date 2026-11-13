/** Pinned native transform declaration/number serialization comparisons. */
import assert from 'node:assert/strict';
import{fileURLToPath}from'node:url';
import{spawnSyncWithFileInput as spawnSync}from'./process-input.mjs';
import{runNativeBrowser}from'../model/native-browser.mjs';
import{compileJavaScript}from'../model/javascript-ast.mjs';
import{loadGameSource}from'../model/game-source.mjs';
if(!process.argv.includes('--engine'))throw Error('Transform checks require isolated pinned Chromium');
const dv=new DataView(new ArrayBuffer(8));
const bits=n=>{dv.setFloat64(0,n,false);return dv.getBigUint64(0,false).toString();};
const fromBits=b=>{dv.setBigUint64(0,b,false);return dv.getFloat64(0,false);};
const numbers=[0,-0,0.1,-0.1,0.75,1.02,125000.5,125001.5,-125000.5,-125001.5,999999.5,1000000,-1000000,Number.MIN_VALUE,-Number.MIN_VALUE,1e-4,1e-5,1e-6,1e-20,1.234565,1.234575];
for(const base of [0.0001,0.00001,999999,999999.5,0.9999995,0.00009999995,0.2397127693021015]){const b=BigInt(bits(base));for(let offset=-2n;offset<=2n;offset++)numbers.push(fromBits(b+offset));}
let state=0x12345;for(let i=0;i<2048;i++){state=(Math.imul(state,1664525)+1013904223)>>>0;const exponent=(i%1090)-1070;const n=(state/2**32)*2**Math.min(exponent,19);numbers.push(i%2?-n:n);}
const transforms=['none','scale(1,1) rotate(0deg)','translate(-100%,0px)','scale(0.75)','scale(1.02,1.02) rotate(0.2397127693021015deg)',
 'translate(17px,-2px)','translate(17.5px,-0px)','scale(.25,2)','rotate(0)','translate(0,0)','matrix(1,0,0,1,0,0)',
 'scale(1e-2)','scale(1.23456789012345)','rotate(180deg)','scale( 1 , 1 )','SCALE(1.0)','rotate(0.5turn)','translateX(10%)',
 'scaleX(-2) scaleY(3)','translateY(.25px)','rotate(2rad)','rotate(1grad)','scale(125000.5)','scale(-125001.5)',
 'scale(1)translate(2px,3px)','\t scale(+01.00) \n','scale(1.)','scale()','scale(1,2,3)','translate(1)','rotate(1)',
 'scale(100%)','rotate(1px)','translate(2deg)','scale(NaN)','scale(Infinity)','scale(0x10)','scale(1e)','scale(1e+)',
 'scale (1)','scale(1','scale(1))','scale(1) nonsense','none scale(1)','scale(1 2)','translate(,1px)'];
const unsupported=['translate3d(0px,1px,0px)','scale(1000001)','translate(1em)','translate(1cm)','translate(calc(1px + 2px))','scale(var(--x))','scale(1/*c*/)'];
const native=runNativeBrowser(function(input){return{
 numbers:input.numbers.map(text=>{var e=document.createElement('div');e.style.transform='scale('+text+')';if(!e.style.transform)throw Error('Native rejected numeric fixture '+text);return{text:e.style.transform.slice(6,-1)};}),
 transforms:input.transforms.map(text=>{var e=document.createElement('div');e.style.transform=text;return e.style.transform?{status:'complete',text:e.style.transform}:{status:'invalid'};})};}.toString(),{numbers:numbers.map(n=>String(n)),transforms},{allowInlineStyles:true});
const requests=[...numbers.map(n=>({operation:'css-number',bits:bits(n)})),...transforms.map(source=>({operation:'transform',source})),...unsupported.map(source=>({operation:'transform',source}))];
const child=spawnSync(fileURLToPath(new URL('.lake/build/bin/jscsscheck',import.meta.url)),[],{input:JSON.stringify(requests),encoding:'utf8',timeout:120000,maxBuffer:8*1024*1024});
if(child.error)throw child.error;assert.equal(child.status,0,child.stderr);const actual=JSON.parse(child.stdout),failures=[];
for(let i=0;i<requests.length;i++)try{if(i<numbers.length)assert.deepEqual(actual[i],native.result.numbers[i]);else if(i<numbers.length+transforms.length)assert.deepEqual(actual[i],native.result.transforms[i-numbers.length]);else assert.equal(actual[i].status,'unresolved');}catch(error){failures.push({request:requests[i],observed:actual[i],expected:i<numbers.length?native.result.numbers[i]:native.result.transforms[i-numbers.length],error:error.message});}
const sourceCases=[];const add=(name,source,expectedStatus)=>sourceCases.push({name,source,expectedStatus});
for(const value of transforms)add(`native transform ${value}`,`var e=document.createElement('div');e.style.transform=${JSON.stringify(value)};[e.style.transform,e.style.webkitTransform,e.style.cssText,e.getAttribute('style')].join('|');`);
add('native prefixed alias stores canonical property',`var e=document.createElement('div');e.style.webkitTransform='scale(0.75)';[e.style.transform,e.style.cssText,e.style.item(0)].join('|');`);
add('native CSS alias setter and removal',`var e=document.createElement('div');e.style.setProperty('-webkit-transform','translate(-100%,0px)','important');var before=[e.style.getPropertyValue('transform'),e.style.getPropertyPriority('-webkit-transform')].join('|');before+'|'+e.style.removeProperty('-webkit-transform')+'|'+e.style.cssText;`);
add('source conversion returns original assignment object',`var e=document.createElement('div'),v={toString:function(){return 'scale(1.02)';}};var original=(e.style.transform=v);(original===v)+':'+e.style.transform;`);
add('direct null clears transform',`var e=document.createElement('div');e.style.transform='scale(1)';e.style.transform=null;e.style.transform;`);
add('object null is invalid string and preserves transform',`var e=document.createElement('div');e.style.transform='scale(1)';e.style.transform={toString:function(){return null;}};e.style.transform;`);
add('undefined preserves transform',`var e=document.createElement('div');e.style.transform='scale(1)';e.style.transform=undefined;e.style.transform;`);
add('nested conversion mutation and throw',`var e=document.createElement('div');e.style.transform='scale(1)';try{e.style.transform={toString:function(){e.style.transform='scale(2)';throw 'stop';}};}catch(x){}e.style.transform;`);
add('raw attribute survives reading CSSOM',`var e=document.createElement('div');e.setAttribute('style','transform:scale(1.23456789012345)');e.style.transform+'|'+e.getAttribute('style');`);
add('other property write serializes transform',`var e=document.createElement('div');e.style.transform='scale(1.23456789012345)';e.style.opacity='1';e.style.transform+'|'+e.getAttribute('style');`);
add('duplicate transform priority in cssText',`var e=document.createElement('div');e.style.cssText='transform:scale(2)!important;transform:scale(3)';e.style.cssText;`);
const main=loadGameSource().sources['main.js'];
const meterSource=main.split('\n').find(line=>line.includes("Game.ascendMeter.style.transform="));
const cookieSource=main.split('\n').find(line=>line.includes("Game.l.style.transform='scale('"));
assert.ok(meterSource&&cookieSource);
for(const percent of [0,0.25,0.333333333333,0.99,1,1.5,-1])add(`actual ascendMeter source ${percent}`,
 `var Game={ascendMeter:document.createElement('div'),ascendMeterPercent:${percent}};${meterSource};Game.ascendMeter.style.transform;`);
for(const frame of [0,1,5,30])for(const pulse of [0,1])add(`actual bigCookie source frame=${frame} pulse=${pulse}`,
 `var Game={l:document.createElement('div'),T:${frame}},pulse=${pulse};${cookieSource};Game.l.style.transform;`);
add('known transform still cannot supply geometry',`var e=document.createElement('div');document.body.appendChild(e);e.style.transform='scale(1)';e.getBoundingClientRect();`,'unresolved');
for(const source of unsupported)add(`unsupported native declaration ${source}`,`var e=document.createElement('div');e.style.transform=${JSON.stringify(source)};e.style.transform;`,'unresolved');
const nativeSources=runNativeBrowser(function(cases){return cases.map(c=>{if(c.expectedStatus)return{status:c.expectedStatus};document.body.textContent='';try{var value=(function(){return eval(c.source);})();return{status:'complete',value:{type:'string',units:Array.from({length:value.length},(_,i)=>value.charCodeAt(i))}};}catch(e){return{status:'throw',name:e.name};}});}.toString(),sourceCases,{allowEval:true,allowInlineStyles:true});
const units=text=>Array.from({length:text.length},(_,i)=>text.charCodeAt(i));
const sourceRequests=sourceCases.map(c=>({browserLibrary:true,fuel:100000,loadedStylesheets:[],initialHtmlUnits:units('<!doctype html><html><head></head><body></body></html>'),ast:compileJavaScript(c.source,{name:c.name})}));
const sourceChild=spawnSync(fileURLToPath(new URL('.lake/build/bin/jsastcheck',import.meta.url)),['--execute'],{input:JSON.stringify(sourceRequests),encoding:'utf8',timeout:120000,maxBuffer:8*1024*1024});
if(sourceChild.error)throw sourceChild.error;assert.equal(sourceChild.status,0,sourceChild.stderr);const sourceActual=JSON.parse(sourceChild.stdout);let sourceFailures=0;
for(let i=0;i<sourceCases.length;i++)try{if(sourceCases[i].expectedStatus)assert.equal(sourceActual[i].status,sourceCases[i].expectedStatus);else assert.deepEqual({status:sourceActual[i].status,value:sourceActual[i].value},nativeSources.result[i]);}catch(error){sourceFailures++;failures.push({source:sourceCases[i].name,observed:sourceActual[i],expected:nativeSources.result[i],error:error.message});}
if(failures.length){console.error(JSON.stringify(failures.slice(0,30),null,2));process.exitCode=1;}
console.log(JSON.stringify({cases:requests.length,passed:requests.length-(failures.length-sourceFailures),browserCases:sourceCases.length,browserPassed:sourceCases.length-sourceFailures,nativeComparisons:numbers.length+transforms.length,versions:native.versions,executableHash:native.executableHash,transformGeometryVerified:false,rendererRefinementVerified:false}));

/** Isolated drawImage admission/source snapshots. No pixel or origin-clean oracle. */
import assert from 'node:assert/strict';
import {readFileSync} from 'node:fs';
import {join} from 'node:path';
import {fileURLToPath} from 'node:url';
import {createHash} from 'node:crypto';
import {spawnSyncWithFileInput} from './process-input.mjs';
import {compileJavaScript} from '../model/javascript-ast.mjs';
import {loadGameSource} from '../model/game-source.mjs';
import {runNativeBrowser} from '../model/native-browser.mjs';
if(!process.argv.includes('--engine'))throw Error('This checker requires isolated pinned Chromium');
const cases=[],add=(name,body,extra={})=>cases.push({name,body,...extra});
const prefix='var c=document.createElement("canvas"),x=c.getContext("2d"),s=document.createElement("canvas"),y=s.getContext("2d");';
for(let n=0;n<=11;n++){const args=n?['s',...Array.from({length:n-1},(_,i)=>`arg(${i+1})`)]:[];
 add('overload count '+n,`var log='';function arg(n){return {valueOf:function(){log+=n+',';return 1;}};}try{log+='r'+typeof x.drawImage(${args.join(',')});}catch(e){log+=e.name;}return log;`,{commands:[3,5,9,10,11].includes(n)?1:0});}
for(const source of ['null','undefined','1','"image"','{}','document.createElement("div")'])add('source union '+source,
 `var log='';try{x.drawImage(${source},{valueOf:function(){log+='wrong';return 0;}},0);}catch(e){log+=e.name;}return log;`,{commands:0});
add('source union rejects forged prototype',`var log='';try{x.drawImage(Object.create(HTMLImageElement.prototype),{valueOf:function(){log+='wrong';return 0;}},0);}catch(e){log+=e.name;}return log;`,{commands:0});
add('context brand precedes conversion',`var log='';try{CanvasRenderingContext2D.prototype.drawImage.call({},s,{valueOf:function(){log+='wrong';return 0;}},0);}catch(e){log+=e.name;}return log;`,{commands:0});
add('not a constructor',`var f=x.drawImage;try{new f(s,0,0);}catch(e){return e.name;}`,{commands:0});
add('all numeric args convert in order after NaN',`var log='';function a(n,v){return {valueOf:function(){log+=n;return v;}};}x.drawImage(s,a('a',NaN),a('b',1),a('c',2),a('d',3),a('e',4),a('f',5),a('g',6),a('h',7));return log;`,{commands:0});
add('numeric exception stops later conversions',`var log='';try{x.drawImage(s,{valueOf:function(){log+='a';return 1;}},{valueOf:function(){log+='b';throw 'stop';}},{valueOf:function(){log+='wrong';return 1;}},2);}catch(e){log+=e;}return log;`,{commands:0});
add('extra arguments are not converted',`var log='';x.drawImage(s,0,0,1,1,0,0,1,1,{valueOf:function(){log+='wrong';return 0;}});return log;`,{commands:1});
for(const tw of [0,2])for(const sw of [0,2])add(`zero-source error order target${tw} source${sw}`,
 `c.width=${tw};s.width=${sw};var log='';try{x.drawImage(s,{valueOf:function(){log+='n';return NaN;}},0);log+='ok';}catch(e){log+=e.name;}return log;`,{commands:0,...(sw===0?{expectedStatus:'unresolved'}:{})});
add('source zero height DOMException stays explicit',`s.height=0;try{x.drawImage(s,0,0);}catch(e){return e.name;}`,{expectedStatus:'unresolved'});
add('numeric conversion empties source before native validation',`var log='';try{x.drawImage(s,{valueOf:function(){s.width=0;log+='a';return 0;}},{valueOf:function(){log+='b';return 0;}});}catch(e){log+=e.name;}return log;`,{expectedStatus:'unresolved'});
add('numeric conversion empties destination',`x.drawImage(s,{valueOf:function(){c.width=0;return 0;}},0);return c.width;`,{commands:0});
add('numeric conversion expands source before capture',`x.drawImage(s,{valueOf:function(){s.width=17;return 0;}},0);return s.width;`,{commands:1,sourceWidth:17});
add('numeric conversion paints source before capture',`x.drawImage(s,{valueOf:function(){y.fillRect(1,2,3,4);return 0;}},0);return x.fillStyle;`,{commands:1,capturedCommands:1});
add('later source painting cannot mutate prior snapshot',`y.fillRect(1,2,3,4);x.drawImage(s,0,0);y.fillRect(5,6,7,8);return x.fillStyle;`,{commands:1,capturedCommands:1});
add('later source resize cannot mutate prior snapshot',`s.width=17;y.fillRect(1,2,3,4);x.drawImage(s,0,0);s.width=23;return s.width;`,{commands:1,capturedCommands:1,sourceWidth:17});
add('self-copy uses finite earlier scene',`x.fillRect(1,2,3,4);x.drawImage(c,0,0);x.drawImage(c,0,0);return x.fillStyle;`,{commands:3,capturedCommands:2});
add('source no context is a blank scene without creating context',`s=document.createElement('canvas');x.drawImage(s,0,0);return s.width;`,{commands:1,capturedCommands:0});
add('source alpha false is captured',`s=document.createElement('canvas');y=s.getContext('2d',{alpha:false});x.drawImage(s,0,0);return y.getContextAttributes().alpha;`,{commands:1,sourceAlpha:false});
add('target alpha false is captured',`c=document.createElement('canvas');x=c.getContext('2d',{alpha:false});x.drawImage(s,0,0);return x.getContextAttributes().alpha;`,{lastDestination:true,commands:1,targetAlpha:false});
add('saved state does not erase image commands',`x.save();x.globalAlpha=0.25;x.rotate(0.1);x.drawImage(s,0,0);x.restore();return x.globalAlpha;`,{commands:1,unknown:true});
add('later transform reset preserves image history',`x.rotate(0.1);x.drawImage(s,0,0);x.resetTransform();return x.fillStyle;`,{commands:1,unknown:true});
add('dimension reset erases destination image commands',`x.drawImage(s,0,0);c.width=c.width;return x.fillStyle;`,{commands:0});
add('empty image returns normally after coercion',`var i=new Image(),log='';x.drawImage(i,{valueOf:function(){log+='a';return 0;}},{valueOf:function(){log+='b';return 0;}});return log;`,{commands:0});
add('pending first image is not yet drawable',`var i=new Image();i.src='img/filler.png';var result=x.drawImage(i,0,0);return typeof result;`,{commands:0});
for(const args of ['NaN,0','Infinity,0','0,0,0,1','0,0,1,0','0,0,-1,-1','0,0,1e300,1e300',
 '0,0,1,1,0,0,0,1','0,0,0,1,0,0,1,1','0,0,-1,-1,0,0,-2,-2','10000,10000,1,1,0,0,1,1',
 '0,0,1e-300,1e-300','0,0,1,1,0,0,1e-300,1e-300']){
 const reject=/NaN|Infinity/.test(args)||['0,0,0,1','0,0,1,0','0,0,1,1,0,0,0,1','0,0,0,1,0,0,1,1'].includes(args);
 add('rectangle admission '+args,`return typeof x.drawImage(s,${args});`,{commands:reject?0:1});
}
for(const args of ['0,0','0,0,20,30','0,0,1,1,0,0,2,3','10,20,-3,-4'])add('loaded image overload '+args,
 `return typeof x.drawImage(img,${args});`,{asset:true,commands:1,sourceKind:'asset'});
add('loaded image returns after source numeric conversion',`var log='';x.drawImage(img,{valueOf:function(){log+='x';return 0;}},{valueOf:function(){log+='y';return 0;}});return log;`,{asset:true,commands:1,sourceKind:'asset'});
add('loaded image with invalid coordinates records nothing',`return typeof x.drawImage(img,NaN,0);`,{asset:true,commands:0});
add('loaded image draw retains destination unknown transform',`x.rotate(0.1);x.drawImage(img,-256,-256,512,512);x.resetTransform();return x.fillStyle;`,{asset:true,commands:1,unknown:true,sourceKind:'asset'});
add('loaded image request replacement stays explicit',`img.src='img/cursor.png';return typeof x.drawImage(img,0,0);`,{asset:true,expectedStatus:'unresolved'});
add('loaded image src removal stays explicit',`img.removeAttribute('src');return typeof x.drawImage(img,0,0);`,{asset:true,expectedStatus:'unresolved'});
add('canvas readback remains explicit',`x.drawImage(s,0,0);return x.getImageData(0,0,1,1);`,{expectedStatus:'unresolved'});
add('unknown source allocation precedes invalid rectangle',`s.width=100000;return x.drawImage(s,NaN,0);`,{expectedStatus:'unresolved'});
add('target allocation precedes missing source bitmap',`c.width=100000;return x.drawImage(new Image(),0,0);`,{expectedStatus:'unresolved'});
add('video source remains explicit',`return x.drawImage(document.createElement('video'),0,0);`,{expectedStatus:'unresolved'});
add('DOMException code cannot be fabricated',`s.width=0;try{x.drawImage(s,0,0);}catch(e){return e.code;}`,{expectedStatus:'unresolved'});
add('DOMException tag cannot be fabricated',`s.width=0;try{x.drawImage(s,0,0);}catch(e){return Object.prototype.toString.call(e);}`,{expectedStatus:'unresolved'});
add('zero target skips unknown source allocation',`c.width=0;s.width=100000;return typeof x.drawImage(s,0,0);`,{commands:0});
add('zero source preflight precedes unknown destination allocation',`c.width=100000;s.width=0;return x.drawImage(s,0,0);`,{expectedStatus:'unresolved'});
add('responsive image source remains explicit',`img.setAttribute('srcset','img/cursor.png 2x');return x.drawImage(img,0,0);`,{asset:true,expectedStatus:'unresolved'});
add('picture source selection remains explicit',`var p=document.createElement('picture');p.appendChild(img);return x.drawImage(img,0,0);`,{asset:true,expectedStatus:'unresolved'});
add('ordinary JPEG source is admitted by pinned byte audit',`return typeof x.drawImage(img,0,0);`,{asset:true,assetPath:'img/bgBlue.jpg',commands:1,sourceKind:'asset'});
add('PNG eXIf orientation remains explicit',`return x.drawImage(img,0,0);`,{asset:true,assetPath:'img/AQWorlds_CookieClicker_300x40.png',expectedStatus:'unresolved'});
add('GIF frame sampling remains explicit',`return x.drawImage(img,0,0);`,{asset:true,assetPath:'img/tinyglobe.gif',expectedStatus:'unresolved'});
const manifest=JSON.parse(readFileSync(new URL('../model/game-assets.json',import.meta.url)));
const game=loadGameSource(),assets=new Map(),dataURLs={};
for(const path of new Set(cases.filter(c=>c.asset).map(c=>c.assetPath??'img/filler.png'))){
 const asset=manifest.assets.find(a=>a.path===path),bytes=readFileSync(join(game.directory,path));
 assert.equal(createHash('sha256').update(bytes).digest('hex'),asset.sha256);assets.set(path,asset);dataURLs[path]=`data:${asset.mime};base64,${bytes.toString('base64')}`;
}

const native=runNativeBrowser((async function({cases,prefix,dataURLs}){function encode(v){if(typeof v==='number'){var d=new DataView(new ArrayBuffer(8));d.setFloat64(0,v,false);return{type:'number',bits:d.getBigUint64(0,false).toString()};}if(typeof v==='string')return{type:'string',units:Array.from({length:v.length},(_,i)=>v.charCodeAt(i))};if(typeof v==='boolean')return{type:'boolean',value:v};if(typeof v==='undefined')return{type:'undefined'};throw Error('Primitive required');}const results=[];for(const test of cases){if(test.expectedStatus){results.push({status:test.expectedStatus});continue;}const img=new Image();if(test.asset)await new Promise((resolve,reject)=>{img.onload=resolve;img.onerror=reject;img.src=dataURLs[test.assetPath??'img/filler.png'];});results.push((function(){return{status:'complete',value:encode(eval(prefix+'(function(){'+test.body+'})();'))};})());}return results;}).toString(),{cases,prefix,dataURLs},{allowEval:true,allowDataAssets:true});
const requests=cases.map(test=>({browserLibrary:true,diagnosticCanvas:true,fuel:500000,taskFuel:500000,taskBudget:test.asset?1:0,
 ast:compileJavaScript(prefix+(test.asset?'var img=new Image();img.onload=function(){console.log((function(){'+test.body+'})());};img.src='+JSON.stringify(test.assetPath??'img/filler.png')+';':'(function(){'+test.body+'})();'),{name:test.name})}));
const child=spawnSyncWithFileInput(fileURLToPath(new URL('.lake/build/bin/jsastcheck',import.meta.url)),['--execute'],{input:JSON.stringify(requests),encoding:'utf8',timeout:120000,maxBuffer:64*1024*1024});if(child.error)throw child.error;assert.equal(child.status,0,child.stderr);const actual=JSON.parse(child.stdout),failures=[];
for(let i=0;i<cases.length;i++)try{const test=cases[i],observed=actual[i];if(test.expectedStatus){assert.equal(observed.status,test.expectedStatus);continue;}const value=test.asset?observed.consoleEvents.at(-1)?.arguments[0]:observed.value;assert.equal(observed.status,test.asset?'idle':'complete');assert.deepEqual(value,native.result[i].value);const destination=test.lastDestination?observed.diagnosticCanvas.at(-1):observed.diagnosticCanvas[0];assert.equal(destination.commands,test.commands);if(test.commands){const record=destination.commandRecords.at(-1);assert.equal(record.kind,'drawImage');if(test.unknown)assert.equal(record.matrix,null);if(test.capturedCommands!==undefined)assert.equal(record.source.capturedCommands,test.capturedCommands);if(test.sourceWidth!==undefined)assert.equal(record.source.width,test.sourceWidth);if(test.sourceAlpha!==undefined)assert.equal(record.source.alpha,test.sourceAlpha);if(test.targetAlpha!==undefined)assert.equal(record.alpha,test.targetAlpha);if(test.sourceKind){assert.equal(record.source.kind,test.sourceKind);assert.equal(record.source.sha256,assets.get(test.assetPath??'img/filler.png').sha256);assert.equal(record.source.originClean,null);}}}catch(error){failures.push({name:cases[i].name,error:error.message,observed:actual[i],expected:native.result[i]});}
if(failures.length){console.error(JSON.stringify(failures,null,2));process.exitCode=1;}
console.log(JSON.stringify({cases:cases.length,passed:cases.length-failures.length,nativeComparisons:cases.filter(t=>!t.expectedStatus).length,versions:native.versions,immutableSourceSnapshots:true,pixelRefinementVerified:false,originCleanRefinementVerified:false}));

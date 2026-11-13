/** Pinned native drawing-state comparisons; pixels, fonts and paths are separate. */
import assert from 'node:assert/strict';
import {fileURLToPath} from 'node:url';
import {spawnSyncWithFileInput} from './process-input.mjs';
import {compileJavaScript} from '../model/javascript-ast.mjs';
import {runNativeBrowser} from '../model/native-browser.mjs';
import {loadGameSource} from '../model/game-source.mjs';

if(!process.argv.includes('--engine'))throw Error('Canvas comparisons require isolated pinned Chromium');
const cases=[],add=(name,source,extra={})=>cases.push({name,source,...extra});
const prefix='var c=document.createElement("canvas"),x=c.getContext("2d");';
const fields=['globalAlpha','globalCompositeOperation','lineWidth','lineCap','lineJoin','miterLimit',
  'lineDashOffset','shadowOffsetX','shadowOffsetY','shadowBlur','imageSmoothingEnabled',
  'imageSmoothingQuality','textAlign','textBaseline','fillStyle','strokeStyle','shadowColor','filter','font'];
const fingerprint=`[${fields.map(n=>`x.${n}`).join(',')}].join('|')`;
add('native drawing-state defaults',fingerprint);
const values=['undefined','null','false','true','NaN','Infinity','-Infinity','0','-0','1','-1','0.1','0.5','1.5',
  '1e100','-1e100','1e-100','-1e-100','Math.pow(2,-149)','Math.pow(2,-150)',
  '3*Math.pow(2,-150)','1+Math.pow(2,-24)','1+3*Math.pow(2,-24)',
  'Math.pow(2,128)','(Math.pow(2,24)-1)*Math.pow(2,104)','"0.375"'];
for(const name of ['globalAlpha','lineWidth','miterLimit','lineDashOffset','shadowOffsetX','shadowOffsetY','shadowBlur']){
  for(const value of values)add(`${name} ${value}`,`x.${name}=${value};x.${name};`);
  add(`${name} retains old value on invalid write`,`x.${name}=0.25;x.${name}=NaN;x.${name}=Infinity;x.${name};`);
  add(`${name} source numeric conversion`,`var log='';x.${name}={valueOf:function(){log+='n';return 0.25;},toString:function(){log+='wrong';return '1';}};log+':'+x.${name};`);
  add(`${name} conversion failure preserves state`,`x.${name}=0.75;try{x.${name}={valueOf:function(){throw 17;}};}catch(e){}x.${name};`);
}
const keywords={globalCompositeOperation:['clear','copy','source-over','source-in','source-out','source-atop',
  'destination-over','destination-in','destination-out','destination-atop','xor','lighter','normal',
  'multiply','screen','overlay','darken','lighten','color-dodge','color-burn','hard-light','soft-light',
  'difference','exclusion','hue','saturation','color','luminosity'],lineCap:['butt','round','square'],
  lineJoin:['miter','round','bevel'],imageSmoothingQuality:['low','medium','high'],
  textAlign:['start','end','left','center','right'],
  textBaseline:['top','hanging','middle','alphabetic','ideographic','bottom']};
for(const [name,options] of Object.entries(keywords)){
  for(const option of [...options,'invalid','',` ${options[0]} `,options[0].toUpperCase()])add(`${name} ${JSON.stringify(option)}`,
    `x.${name}=${JSON.stringify(option)};x.${name};`);
  add(`${name} source string conversion`,`var log='';x.${name}={toString:function(){log+='s';return ${JSON.stringify(options[1])};},valueOf:function(){log+='wrong';return 1;}};log+':'+x.${name};`);
  add(`${name} invalid setter retains previous value`,`x.${name}=${JSON.stringify(options[1])};x.${name}='not a keyword';x.${name};`);
}
for(const value of ['false','true','0','1','null','undefined','""','"false"','{}'])add(`image smoothing boolean ${value}`,
  `x.imageSmoothingEnabled=${value};x.imageSmoothingEnabled;`);
add('boolean conversion does not invoke source methods',`var log='';x.imageSmoothingEnabled={valueOf:function(){log+='wrong';return 0;}};log+':'+x.imageSmoothingEnabled;`);
add('restore on empty stack changes nothing',`x.globalAlpha=0.375;x.restore();x.restore();x.globalAlpha;`);
add('save restore preserves all represented drawing fields',`x.save();x.globalAlpha=0.5;x.globalCompositeOperation='multiply';x.lineWidth=2.5;x.lineCap='round';x.lineJoin='bevel';x.miterLimit=7;x.lineDashOffset=3;x.shadowOffsetX=5;x.shadowOffsetY=-8;x.shadowBlur=12;x.imageSmoothingEnabled=false;x.imageSmoothingQuality='high';x.textAlign='right';x.textBaseline='top';x.restore();${fingerprint};`);
add('nested save and restore order',`x.globalAlpha=0.1;x.save();x.globalAlpha=0.2;x.save();x.globalAlpha=0.3;var out=[x.globalAlpha];x.restore();out.push(x.globalAlpha);x.restore();out.push(x.globalAlpha);x.restore();out.push(x.globalAlpha);out.join('|');`);
add('save and restore ignore extra arguments',`x.save({toString:function(){throw 'wrong';}});x.globalAlpha=0.25;x.restore({valueOf:function(){throw 'wrong';}});x.globalAlpha;`);
add('source conversion can reset the canvas before setter completes',`x.save();x.globalAlpha=0.5;x.lineWidth={valueOf:function(){c.width=17;return 2.5;}};x.restore();x.globalAlpha+':'+x.lineWidth+':'+c.width;`);
add('source conversion can change saved stack before setter completes',`x.globalAlpha=0.5;x.lineWidth={valueOf:function(){x.save();x.globalAlpha=0.25;return 3;}};x.restore();x.globalAlpha+':'+x.lineWidth;`);
add('captured canvas property setter survives constructor replacement',`var Constructor=CanvasRenderingContext2D,set=Object.getOwnPropertyDescriptor(Constructor.prototype,'globalAlpha').set;CanvasRenderingContext2D=function(){};set.call(x,0.25);CanvasRenderingContext2D=Constructor;x.globalAlpha;`);
for(const name of ['save','restore'])add(`${name} receiver check`,`try{CanvasRenderingContext2D.prototype.${name}.call({});}catch(e){e.name;}`);
for(const name of ['globalAlpha','lineWidth','globalCompositeOperation','imageSmoothingEnabled']){
  add(`${name} getter receiver check`,`try{Object.getOwnPropertyDescriptor(CanvasRenderingContext2D.prototype,'${name}').get.call({});}catch(e){e.name;}`);
  add(`${name} setter receiver precedes conversion`,`var log='';try{Object.getOwnPropertyDescriptor(CanvasRenderingContext2D.prototype,'${name}').set.call({}, {toString:function(){log+='wrong';return 'round';},valueOf:function(){log+='wrong';return 0.5;}});}catch(e){log+=e.name;}log;`);
}
for(const mutation of ['c.width=8','c.height=9','c.width=c.width','c.height=c.height',
  'c.setAttribute("width","19")','c.setAttribute("height","20")',
  'c.setAttribute("width","invalid")','c.setAttribute("height","0")']){
  add(`dimension reset ${mutation}`,`x.save();x.globalAlpha=0.5;x.lineWidth=9;${mutation};x.restore();(x===c.getContext('2d'))+':'+x.globalAlpha+':'+x.lineWidth+':'+c.width+':'+c.height;`);
}
for(const name of ['width','height']){
  add(`removing present ${name} resets drawing state`,`c.setAttribute('${name}','19');x.globalAlpha=0.5;x.save();c.removeAttribute('${name}');x.restore();x.globalAlpha+':'+c.${name};`);
  add(`removing absent ${name} preserves drawing state`,`x.globalAlpha=0.5;x.save();c.removeAttribute('${name}');x.globalAlpha=0.25;x.restore();x.globalAlpha;`);
}
add('reset preserves creation alpha',`var other=document.createElement('canvas'),ctx=other.getContext('2d',{alpha:false});ctx.globalAlpha=0.25;ctx.save();other.width=1;ctx.restore();ctx.getContextAttributes().alpha+':'+ctx.globalAlpha;`);
// Source-used fixed-pixel font state, separately from text metrics/rasterization.
for(const value of ['20px Merriweather','9px Merriweather','14px Merriweather','20px Times New Roman',
 '20px "Times New Roman"','20px serif','20px "serif"','20px Arial, serif','0px serif','-0px Arial',
 '20px "unterminated','1024px monospace','','-1px Arial','20px 123','initial','inherit'])add('Canvas native font '+value,
 `x.font='17px Marker';x.font=${JSON.stringify(value)};x.font;`);
for(const expression of ['null','undefined','false','true','17'])add('Canvas font primitive string conversion '+expression,
 `x.font='20px Merriweather';x.font=${expression};x.font;`);
add('Canvas font source ToString order',`var log='';x.font={toString:function(){log+='s';return '20px Merriweather';},valueOf:function(){log+='wrong';return 1;}};log+':'+x.font;`);
add('Canvas font receiver validation precedes ToString',`var log='';try{Object.getOwnPropertyDescriptor(CanvasRenderingContext2D.prototype,'font').set.call({}, {toString:function(){log+='wrong';return '20px Merriweather';}});}catch(e){log+=e.name;}log;`);
add('Canvas font setter without argument preserves old value',`x.font='20px Merriweather';Object.getOwnPropertyDescriptor(CanvasRenderingContext2D.prototype,'font').set.call(x);x.font;`);
add('Canvas font setter is not constructable',`var setter=Object.getOwnPropertyDescriptor(CanvasRenderingContext2D.prototype,'font').set;try{new setter('20px Merriweather');}catch(e){e.name;}`);
add('Canvas font getter ignores arguments',`var log='';var value=Object.getOwnPropertyDescriptor(CanvasRenderingContext2D.prototype,'font').get.call(x,{toString:function(){log+='wrong';return 'x';}});log+':'+value;`);
add('Canvas font conversion failure preserves value',`x.font='14px Merriweather';try{x.font={toString:function(){throw 'stop';}};}catch(e){}x.font;`);
add('Canvas font source conversion resets and writes before outer setter',`x.font='14px Merriweather';x.save();x.font={toString:function(){c.width=17;x.globalAlpha=0.5;x.font='9px serif';return '20px Merriweather';}};x.restore();x.font+':'+x.globalAlpha;`);
add('Canvas font nested save restores parsed state',`x.font='14px Merriweather';x.save();x.font='20px serif';x.save();x.font='9px "serif"';x.restore();var first=x.font;x.restore();first+':'+x.font;`);
add('Canvas font same dimension resets full saved state',`x.font='14px Merriweather';x.save();c.width=c.width;x.restore();x.font;`);
add('Canvas font assignment works on zero-size backing store',`c.width=0;x.font='20px Merriweather';x.font;`);
const fontSourceStatements=loadGameSource().sources['main.js'].split('\n').filter(line=>/ctx\.font='[^']+';/.test(line));
assert.equal(fontSourceStatements.length,5);
for(const [i,statement]of fontSourceStatements.entries())add('actual source Canvas font statement '+i,`var ctx=x;${statement}x.font;`);

const colorFields=['fillStyle','strokeStyle','shadowColor'];
const colorValues=['#fff','#000','#abc','#abcdef','#AbCdEf','#aabbccdd','transparent','red','BLUE',
  'rgb(12, 34, 56)','rgba(255,255,255,0.7)','rgba(5,6,7,0.5)','rgb(50%,0%,100%)','#12','#xyz'];
for(const name of colorFields){
  for(const color of colorValues)add(`${name} native color ${color}`,`x.${name}=${JSON.stringify(color)};x.${name};`);
  for(const opacity of [0,1,2,127,128,254,255]){
    const color='#123456'+opacity.toString(16).padStart(2,'0');
    add(`${name} native alpha byte ${opacity}`,`x.${name}=${JSON.stringify(color)};x.${name};`);
  }
  add(`${name} string conversion order`,`var log='';x.${name}={toString:function(){log+='s';return '#abc';},valueOf:function(){log+='wrong';return 0;}};log+':'+x.${name};`);
  add(`${name} invalid hex preserves previous color`,`x.${name}='#123456';x.${name}='#xyz';x.${name};`);
  add(`${name} receiver validation precedes conversion`,`var log='';try{Object.getOwnPropertyDescriptor(CanvasRenderingContext2D.prototype,'${name}').set.call({}, {toString:function(){log+='wrong';return 'red';}});}catch(e){log+=e.name;}log;`);
  add(`${name} source conversion can reset canvas`,`x.globalAlpha=0.5;x.save();x.${name}={toString:function(){c.width=7;return '#abcdef';}};x.restore();x.globalAlpha+':'+x.${name};`);
  add(`${name} source conversion exception preserves color`,`x.${name}='#abc';try{x.${name}={toString:function(){throw 'stop';}};}catch(e){}x.${name};`);
}
add('save and restore retain parsed Canvas colors',`x.fillStyle='#123';x.strokeStyle='#456';x.shadowColor='#789';x.save();x.fillStyle='red';x.strokeStyle='blue';x.shadowColor='white';x.restore();x.fillStyle+':'+x.strokeStyle+':'+x.shadowColor;`);
add('dimension reset clears Canvas color state',`x.fillStyle='red';x.strokeStyle='blue';x.shadowColor='white';c.width=c.width;x.fillStyle+':'+x.strokeStyle+':'+x.shadowColor;`);

const clearValues=['undefined','null','false','true','NaN','Infinity','-Infinity','0','-0','1','-1','1e100','-1e100','1e-100','"1.25"'];
for(const value of clearValues)add(`clearRect numeric conversion ${value}`,
  `x.globalAlpha=0.375;x.lineWidth=7;var result=x.clearRect(${value},0,10,10);(typeof result)+':'+x.globalAlpha+':'+x.lineWidth;`);
for(const rectangle of ['0,0,0,0','0,0,1,0','0,0,0,1','0,0,-1,-1','10,10,-20,-20',
  'Infinity,0,1,1','0,NaN,1,1','0,0,Infinity,1','0,0,1,NaN'])add(`clearRect rectangle ${rectangle}`,
  `x.save();x.globalAlpha=0.5;var result=x.clearRect(${rectangle});x.restore();(typeof result)+':'+x.globalAlpha;`);
for(const args of ['','0','0,1','0,1,2'])add(`clearRect missing arguments ${args}`,
  `try{x.clearRect(${args});}catch(e){e.name;}`);
add('clearRect checks required argument count before coercion',
  `var log='';try{x.clearRect({valueOf:function(){log+='wrong';return 1;}},0,1);}catch(e){log+=e.name;}log;`);
add('clearRect checks receiver before coercion',
  `var log='';try{CanvasRenderingContext2D.prototype.clearRect.call({}, {valueOf:function(){log+='wrong';return 1;}},0,1,1);}catch(e){log+=e.name;}log;`);
add('clearRect converts all four coordinates in source order even after NaN',
  `var log='';function n(mark,value){return {valueOf:function(){log+=mark;return value;}};}x.clearRect(n('a',NaN),n('b',0),n('c',1),n('d',1));log;`);
add('clearRect stops at a source conversion exception',
  `var log='';try{x.clearRect({valueOf:function(){log+='a';return 0;}},{valueOf:function(){log+='b';throw 'stop';}},{valueOf:function(){log+='wrong';return 1;}},1);}catch(e){log+=e;}log;`);
add('clearRect ignores extra arguments',
  `var log='';x.clearRect(0,0,1,1,{valueOf:function(){log+='wrong';return 1;}});log;`);
add('clearRect source conversion preserves reentrant canvas reset and writes',
  `x.globalAlpha=0.5;x.save();x.clearRect({valueOf:function(){c.width=17;x.globalAlpha=0.25;return 0;}},0,1,1);x.restore();c.width+':'+x.globalAlpha;`);
add('clearRect preserves composite and saved drawing state',
  `x.globalCompositeOperation='copy';x.save();x.globalCompositeOperation='multiply';x.clearRect(0,0,c.width,c.height);x.restore();x.globalCompositeOperation;`);
add('clearRect remains callable after replacing native constructor',
  `var old=CanvasRenderingContext2D,clear=old.prototype.clearRect;CanvasRenderingContext2D=function(){};var result=clear.call(x,0,0,1,1);CanvasRenderingContext2D=old;typeof result;`);
add('canvas pixel readback remains explicit after recorded clear',
  'x.clearRect(0,0,c.width,c.height);x.getImageData(0,0,1,1);',{expectedStatus:'unresolved'});

for(const source of ['x.strokeRect(0,0,1,1);','x.rotate(0.1);x.getTransform();','x.font="20pt Merriweather";',
  'x.fillStyle="currentColor";','x.measureText("cookie");','x.direction;'])add(`explicit remaining boundary ${source}`,source,{expectedStatus:'unresolved'});

const worker=function(input){function encode(v){if(typeof v==='number'){var d=new DataView(new ArrayBuffer(8));d.setFloat64(0,v,false);return{type:'number',bits:d.getBigUint64(0,false).toString()};}if(typeof v==='string')return{type:'string',units:Array.from({length:v.length},(_,i)=>v.charCodeAt(i))};if(typeof v==='boolean')return{type:'boolean',value:v};throw Error('Expected primitive result');}
return input.cases.map(function(c){if(c.expectedStatus)return{status:c.expectedStatus};try{return{status:'complete',value:encode((function(){return eval(input.prefix+c.source);})())};}catch(e){return{status:'throw',name:e.name,message:e.message};}});};
const native=runNativeBrowser(worker.toString(),{cases,prefix},{allowEval:true});
const requests=cases.map(c=>({browserLibrary:true,fuel:300000,ast:compileJavaScript(prefix+c.source,{name:c.name})}));
const child=spawnSyncWithFileInput(fileURLToPath(new URL('.lake/build/bin/jsastcheck',import.meta.url)),['--execute'],{input:JSON.stringify(requests),encoding:'utf8',timeout:120000,maxBuffer:32*1024*1024});
if(child.error)throw child.error;assert.equal(child.status,0,child.stderr);const actual=JSON.parse(child.stdout),failures=[];
for(let i=0;i<cases.length;i++)try{if(cases[i].expectedStatus)assert.equal(actual[i].status,cases[i].expectedStatus);else assert.deepEqual({status:actual[i].status,value:actual[i].value},native.result[i]);}catch(error){failures.push({name:cases[i].name,observed:actual[i],expected:native.result[i],error:error.message});}
if(failures.length){console.error(JSON.stringify(failures,null,2));process.exitCode=1;}
console.log(JSON.stringify({cases:cases.length,passed:cases.length-failures.length,nativeComparisons:cases.filter(c=>!c.expectedStatus).length,versions:native.versions,executableHash:native.executableHash,gameEntryPointExecuted:false,rendererRefinementVerified:false}));

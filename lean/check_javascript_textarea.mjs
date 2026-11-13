/** Native parsed-textarea values, dirty flags, reflection and source conversions. */
import assert from 'node:assert/strict';
import {fileURLToPath} from 'node:url';
import {spawnSyncWithFileInput} from './process-input.mjs';
import {compileJavaScript} from '../model/javascript-ast.mjs';
import {runNativeBrowser} from '../model/native-browser.mjs';

if(!process.argv.includes('--engine'))throw Error('Textarea checks require isolated pinned Chromium');
const cases=[],add=(name,source,expectedStatus)=>cases.push({name,source,expectedStatus});
const prefix='var c=document.createElement("textarea");';
const quote=value=>JSON.stringify(value).replaceAll(String.fromCharCode(8232),String.fromCharCode(92)+'u2028')
  .replaceAll(String.fromCharCode(8233),String.fromCharCode(92)+'u2029');
const fingerprint='[c.value,c.defaultValue,c.textContent,c.textLength,c.selectionStart,c.selectionEnd,c.selectionDirection,c.readOnly,c.disabled,c.required,c.type].join("|")';
add('native defaults',fingerprint);
const texts=['','cookie','A\rB','A\r\nB','\r\r\n\n','\nA','\n\nA','\tA\t','<b>x</b>','a&b','\u0000','\ud800','\udfff','\ud83c\udf6a','a\u2028b\u2029c'];
for(const text of texts){
  for(const property of ['value','defaultValue','textContent'])add(`${property} UTF16 ${JSON.stringify(text)}`,
    `c.${property}=${quote(text)};${fingerprint};`);
  add(`dirty value survives new default ${JSON.stringify(text)}`,
    `c.defaultValue='before';c.value=${quote(text)};c.defaultValue='after';${fingerprint};`);
  add(`same value assignment sets dirty flag ${JSON.stringify(text)}`,
    `c.defaultValue=${quote(text)};c.value=c.value;c.defaultValue='after';${fingerprint};`);
}
for(const content of ['A%2BB!END!','\nA','\r\nA\r\nB','\n\nA','&lt;b&gt;&amp;&#39;','<b id="literal">A</b>']){
  const html='<textarea readonly>'+content+'</textarea>';
  add(`parsed native export RCDATA ${JSON.stringify(content)}`,
    `var host=document.createElement('div');host.innerHTML=${JSON.stringify(html)};c=host.firstChild;${fingerprint};`);
}
for(const property of ['value','defaultValue'])for(const value of ['null','undefined','false','true','17','-0','NaN','Infinity',
  '{toString:function(){return null;}}','{toString:function(){return "A\\r\\nB";}}']){
  add(`${property} source conversion ${value}`,`c.${property}=${value};${fingerprint};`);
}
for(const property of ['value','defaultValue']){
  add(`${property} receiver before source conversion`,
    `var log='';try{Object.getOwnPropertyDescriptor(HTMLTextAreaElement.prototype,'${property}').set.call({}, {toString:function(){log+='wrong';return 'x';}});}catch(e){log+=e.name;}log;`);
  add(`${property} reentrant conversion updates current state`,
    `var log='';c.${property}={toString:function(){log+='s';c.defaultValue='nested';c.value='dirty';return 'outer';},valueOf:function(){log+='wrong';return 'other';}};log+':'+${fingerprint};`);
  add(`${property} conversion exception retains nested writes`,
    `try{c.${property}={toString:function(){c.value='nested';throw 'stop';}};}catch(e){}${fingerprint};`);
  add(`${property} source conversion returns original assignment object`,
    `var object={toString:function(){return 'cookie';}};var same=(c.${property}=object)===object;String(same)+':'+${fingerprint};`);
}
for(const property of ['readOnly','disabled','required']){
  const attr=property.toLowerCase();
  for(const value of ['false','true','0','1','null','undefined','""','"false"','{}'])add(`${property} boolean ${value}`,
    `c.${property}=${value};${fingerprint}+':'+c.getAttribute('${attr}');`);
  add(`${property} object truthiness has no callbacks`,
    `var log='';c.${property}={valueOf:function(){log+='wrong';return false;},toString:function(){log+='wrong';return '';}};log+':'+${fingerprint};`);
  add(`${property} attribute presence is true even for false text`,
    `c.setAttribute('${attr}','false');var before=c.${property};c.removeAttribute('${attr}');String(before)+':'+${fingerprint};`);
}
add('direct text children determine default value',
  `var a=document.createTextNode('A'),comment=document.createComment('ignored'),b=document.createTextNode('B');c.appendChild(a);c.appendChild(comment);c.appendChild(b);${fingerprint};`);
add('nested element text is not part of default value',
  `var e=document.createElement('b');e.textContent='nested';c.appendChild(document.createTextNode('A'));c.appendChild(e);c.appendChild(document.createTextNode('B'));${fingerprint};`);
add('direct text child mutation updates a nondirty value',
  String.raw`var t=document.createTextNode('before');c.appendChild(t);t.nodeValue='A\rB';${fingerprint};`);
add('direct text mutation retains a dirty value',
  `var t=document.createTextNode('before');c.appendChild(t);c.value='edited';t.nodeValue='after';${fingerprint};`);
add('direct text removal updates default and nondirty value',
  `var a=document.createTextNode('A'),b=document.createTextNode('B');c.appendChild(a);c.appendChild(b);c.removeChild(a);${fingerprint};`);
add('innerHTML changes the nondirty value', String.raw`c.innerHTML='A&amp;B\n&lt;x&gt;';${fingerprint};`);
add('innerHTML preserves a dirty value', `c.value='edited';c.innerHTML='A&amp;B';${fingerprint};`);
add('same normalized value preserves existing selection',
  String.raw`c.value='A\nB';c.value='A\r\nB';${fingerprint};`);
add('captured native getter retains brand after global replacement',
  `c.value='cookie';var Original=HTMLTextAreaElement,get=Object.getOwnPropertyDescriptor(Original.prototype,'value').get;HTMLTextAreaElement=function(){};var value=get.call(c);HTMLTextAreaElement=Original;value;`);
add('detached textarea focus has no effect','c.focus();typeof c.value;');
for(const operation of ['c.select();','c.setSelectionRange(0,1);','c.selectionStart=1;'])
  add(`detached cached selection ${operation}`,operation+fingerprint+';');
add('editing range remains explicit','c.setRangeText("x");','unresolved');

const native=runNativeBrowser(function(input){
  return input.cases.map(c=>{
    if(c.expectedStatus)return {status:c.expectedStatus};
    const value=(function(){return eval(input.prefix+c.source);})();
    if(typeof value!=='string')throw Error('Expected string result: '+c.name);
    return {status:'complete',value:{type:'string',units:Array.from({length:value.length},(_,i)=>value.charCodeAt(i))}};
  });
}.toString(),{prefix,cases},{allowEval:true});
const requests=cases.map(c=>({browserLibrary:true,fuel:500000,ast:compileJavaScript(prefix+c.source,{name:c.name})}));
const child=spawnSyncWithFileInput(fileURLToPath(new URL('.lake/build/bin/jsastcheck',import.meta.url)),['--execute'],{
  input:JSON.stringify(requests),encoding:'utf8',timeout:120000,maxBuffer:32*1024*1024});
if(child.error)throw child.error;
assert.equal(child.status,0,child.stderr||child.stdout);
const actual=JSON.parse(child.stdout),failures=[];
for(let i=0;i<cases.length;i++)try{
  if(cases[i].expectedStatus)assert.equal(actual[i].status,cases[i].expectedStatus);
  else assert.deepEqual({status:actual[i].status,value:actual[i].value},native.result[i]);
}catch(error){failures.push({name:cases[i].name,observed:actual[i],expected:native.result[i],error:error.message});}
if(failures.length){console.error(JSON.stringify(failures.slice(0,20),null,2));process.exitCode=1;}
console.log(JSON.stringify({cases:cases.length,passed:cases.length-failures.length,
  nativeComparisons:cases.filter(c=>!c.expectedStatus).length,versions:native.versions,
  executableHash:native.executableHash,formControlRefinementVerified:false}));

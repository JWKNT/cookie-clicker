/** Dynamic Function parser comparisons; not a universal parser-refinement proof. */
import assert from 'node:assert/strict';
import { spawnSyncWithFileInput as spawnSync } from './process-input.mjs';
import { fileURLToPath } from 'node:url';
import { compileJavaScript } from '../model/javascript-ast.mjs';
import { loadGameSource } from '../model/game-source.mjs';
import { runNativeEngine } from '../model/native-engine.mjs';

const source = loadGameSource();
const plural = /"plural-forms":\s*"([^"]+)"/.exec(source.sources['loc/EN.js'])?.[1];
assert.equal(plural,'nplurals=2;plural=(n!=1);');
assert(source.sources['main.js'].includes("return new Function('n','var plural, nplurals; '+ plural_form +' return plural;');"));
const body = 'var plural, nplurals; '+plural+' return plural;';
const b = JSON.stringify(body);
const factory = `new Function("n",${b})`;
const cases=[];
const add=(name,text,extra={})=>cases.push({name,source:text,...extra});
add('actual EN boolean plural decisions',`var f=${factory};[f(-1),f(0),f(1),f(2),f("1"),f("2"),f(null),f(undefined),f(NaN),f(Infinity),f(true),f(false)].join(":");`);
add('dynamic closure native identity and basic fields',`var f=${factory};typeof f+":"+f.name+":"+f.length+":"+(f instanceof Function)+":"+(f.prototype.constructor===f);`);
add('native anonymous wrapper source is retained',`var f=${factory};Function.prototype.toString.call(f);`);
add('native anonymous source ignores name mutation',`var f=${factory};Object.defineProperty(f,"name",{value:"changed"});Function.prototype.toString.call(f);`);
add('call and construct Function share compiled behavior',`var a=Function("n",${b}),b=${factory};(a!==b)+":"+(a.prototype!==b.prototype)+":"+a(1)+":"+b(2);`);
add('constructor arguments convert left to right once',`var log="",f=new Function({toString:function(){log+="p";return "n";}},{toString:function(){log+="b";return ${b};}});log+":"+f(1);`);
add('parameter conversion throw skips body conversion',`var log="";try{new Function({toString:function(){log+="p";throw 7;}},{toString:function(){log+="b";return ${b};}});}catch(e){log+=e;}log;`);
add('source ToPrimitive fallback preserves string hint order',`var log="",f=Function({toString:function(){log+="s";return {};},valueOf:function(){log+="v";return "n";}},{toString:function(){log+="b";return ${b};}});log+":"+f(2);`);
add('compiled declarations do not mutate caller or global variables',`var plural="global",nplurals="global2";function outer(){var plural="local",nplurals="local2",f=${factory};return f(1)+":"+plural+":"+nplurals;}outer()+":"+plural+":"+nplurals;`);
add('generated source function supports ordinary construction',`var f=${factory},o=new f(1);typeof o+":"+(o instanceof f);`);
add('generated comparison invokes source valueOf',`var log="",f=${factory};var answer=f({valueOf:function(){log+="v";return 1;}});log+":"+answer;`);
add('generated comparison uses toString fallback',`var log="",f=${factory};var answer=f({valueOf:function(){log+="v";return {};},toString:function(){log+="s";return "2";}});log+":"+answer;`);
add('generated comparison propagates source exceptions',`var f=${factory},out="";try{f({valueOf:function(){throw 9;}});}catch(e){out+=e;}out+":"+f(1);`);
add('compiled function accepts generic call receiver and argument',`var f=${factory};Function.prototype.call.call(f,{n:2},1)+":"+Function.prototype.apply.call(f,null,[2]);`);
add('source conversion exception precedes unsupported compilation','try{Function({toString:function(){throw 5;}},"return 3;");}catch(e){e+"";}');
add('ordinary dynamic arithmetic body','Function("n","return n+1;")(4)+"";');
add('different valid parameter name compiles',`var f=Function("m",${b});typeof f+":"+f.length;`);
add('zero arguments creates an empty function','var f=Function();f.length+":"+f()+":"+Function.prototype.toString.call(f);');
add('one body argument has no formal parameters','var f=Function("return 7;");f.length+":"+f();');
add('variadic formal strings join with commas','var f=Function("a","b,c","return a+2*b+3*c;");f.length+":"+f(1,2,3)+":"+Function.prototype.toString.call(f);');
add('formal list permits native trailing comma','var f=Function("a,","return a;");f.length+":"+f(9);');
add('formal line comment ends at the constructor newline','var f=Function("a// rest","b","return a;");f.length+":"+f(9)+":"+Function.prototype.toString.call(f);');
add('body line comment ends before closing wrapper','var f=Function("return 3;// final comment");f()+":"+Function.prototype.toString.call(f);');
add('duplicate sloppy parameters retain argument alias order',String.raw`Function("a,a","return a+\":\"+arguments[0]+\":\"+arguments[1];")(1,2);`);
add('strict dynamic body keeps undefined this',String.raw`Function("\"use strict\";return typeof this;")();`);
add('dynamic function uses global scope rather than caller scope','var dynamicScopeValue=9;function caller(){var dynamicScopeValue=7;return Function("return dynamicScopeValue;")();}caller()+"";');
add('dynamic anonymous name is not a lexical self binding','Function("return typeof anonymous;")();');
add('nested dynamic source closure and recursion','Function("n","function f(x){return x<2?1:x*f(x-1);}return f(n);")(5)+"";');
add('dynamic body parses a regular expression',String.raw`Function("return /ab+/.test(\"abb\");")()+"";`);
add('dynamic length descriptor is configurable','var f=Function("a,b","return a;");var d=Object.getOwnPropertyDescriptor(f,"length");d.value+":"+d.writable+":"+d.enumerable+":"+d.configurable;');
add('strict duplicate parameters throw syntax error',String.raw`try{Function("a,a","\"use strict\";return a;");}catch(e){e.name;}`);
add('strict eval parameter throws syntax error',String.raw`try{Function("eval","\"use strict\";return 1;");}catch(e){e.name;}`);
add('strict arguments parameter throws syntax error',String.raw`try{Function("arguments","\"use strict\";return 1;");}catch(e){e.name;}`);
add('keyword parameter throws syntax error','try{Function("for","return 1;");}catch(e){e.name;}');
add('parameter closing token cannot escape into body','try{Function("a) { return 9; } //","return 1;");}catch(e){e.name;}');
add('block comment cannot cross formal and body boundary','try{Function("a/*","*/return a;");}catch(e){e.name;}');
add('all argument conversions precede syntax checking','var log="";try{Function({toString:function(){log+="p";return "a)";}},{toString:function(){log+="b";throw 8;}});}catch(e){log+=e;}log;');
add('invalid dynamic body is a source syntax exception','try{Function("return );");}catch(e){e.name;}');
add('dynamic body runtime exception is not a parse error','try{Function("return dynamicMissingValue;")();}catch(e){e.name;}');
add('modern default parameter grammar remains explicit','Function("a=1","return a;");',{expectedStatus:'unresolved'});
add('modern rest parameter grammar remains explicit','Function("...args","return args;");',{expectedStatus:'unresolved'});
add('modern destructured parameter grammar remains explicit','Function("{a}","return a;");',{expectedStatus:'unresolved'});
add('legacy dynamic caller inspection stays explicit',`var f=${factory};f.caller;`,{expectedStatus:'unresolved'});
add('dynamic function inherits ordinary call',`var f=${factory};f.call(null,1)+"";`);

const result=spawnSync(fileURLToPath(new URL('.lake/build/bin/jsastcheck',import.meta.url)),['--execute'],{
 input:JSON.stringify(cases.map(c=>({ast:compileJavaScript(c.source,{name:c.name}),fuel:200000,standardLibrary:true}))),
 encoding:'utf8',timeout:120000,maxBuffer:8*1024*1024,
});
if(result.error)throw result.error;assert.equal(result.status,0,result.stderr);
const actual=JSON.parse(result.stdout);
const nativeCases=cases.filter(c=>!c.expectedStatus);
const expected=runNativeEngine(`const fs=require('fs'),vm=require('vm');const input=JSON.parse(fs.readFileSync(0,'utf8'));process.stdout.write(JSON.stringify(input.map(c=>{const value=vm.runInNewContext(c.source);if(typeof value!=='string')throw Error(c.name);return {name:c.name,units:Array.from({length:value.length},(_,i)=>value.charCodeAt(i))};})));`,nativeCases);
const byName=new Map(expected.map(c=>[c.name,c.units]));
for(let i=0;i<cases.length;i++){
 const c=cases[i];assert.equal(actual[i].status,c.expectedStatus||'complete',c.name+': '+JSON.stringify(actual[i]));
 if(!c.expectedStatus)assert.deepEqual(actual[i].value,{type:'string',units:byName.get(c.name)},c.name);
}
console.log(JSON.stringify({dynamicFunctionCases:cases.length,nativeComparisons:nativeCases.length,
 sourceHashes:source.hashes,pinnedEnglishCase:{parameters:['n'],body},generalDynamicParserVerified:false}));

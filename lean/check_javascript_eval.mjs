/** Source-AST execution comparisons. These finite checks are not a full-game proof. */
import assert from 'node:assert/strict';
import { spawnSyncWithFileInput as spawnSync } from './process-input.mjs';
import { fileURLToPath } from 'node:url';
import vm from 'node:vm';
import { compileJavaScript, compilePinnedGameAst, numberLiteralBits } from '../model/javascript-ast.mjs';
import { loadGameSource } from '../model/game-source.mjs';
import { inspectNativeEngine, runNativeEngine } from '../model/native-engine.mjs';
import { runNativeBrowser } from '../model/native-browser.mjs';

const cases = [];
const add = (name, source, extra = {}) => cases.push({ name, source, fuel: 200000, ...extra });
add('closure survives its parent return', 'function outer(x){return function(y){x+=y;return x;};}var f=outer(3);f(4);f(5);');
add('closure captures later binding updates', 'var x=1;function f(){return x;}x=9;f();');
add('assignment evaluates reference once before rhs', 'var log="",o={x:1};function base(){log+="b";return o;}function key(){log+="k";return "x";}function rhs(){log+="r";return 4;}var old=base()[key()]++;base()[key()]+=rhs();log+":"+old+":"+o.x;');
add('postfix and prefix update return different values', 'var x=2;var a=x++;var b=++x;a*100+b*10+x;');
add('for continue executes update', 'var sum=0;for(var i=0;i<5;i++){if(i===2)continue;sum+=i;}sum;');
add('nested labeled loop control', 'var n=0;outer:for(var i=0;i<4;i++){var j=0;while(j<5){j++;if(j===2)continue outer;if(i===3)break outer;n++;}}n;');
add('do while executes body before test', 'var x=0;do{x++;}while(x<3);x;');
add('catch scope preserves outer binding', 'var e=7;try{throw 3;}catch(e){e+=1;}e;');
add('finally preserves return', 'function f(){try{return 3;}finally{var x=4;}}f();');
add('finally overrides return', 'function f(){try{return 3;}finally{return 8;}}f();');
add('finally runs on continue', 'var n=0;for(var i=0;i<3;i++){try{continue;}finally{n++;}}n;');
add('finally propagates its own throw', 'function f(){try{return 3;}finally{throw 9;}}f();');
add('getters and setters preserve receiver', 'var o={v:2,get x(){return this.v+1;},set x(n){this.v=n*2;}};o.x=4;o.x;');
add('method call binds receiver', 'var tag="global";var o={tag:"object",f:function(){return this.tag;}};o.f();');
add('logical result loses property reference', 'var tag="global";var o={tag:"object",f:function(){return this.tag;}};(true&&o.f)();');
add('conditional result loses property reference', 'var tag="global";var o={tag:"object",f:function(){return this.tag;}};(true?o.f:null)();');
add('comma result loses property reference', 'var tag="global";var o={tag:"object",f:function(){return this.tag;}};(0,o.f)();');
add('strict bare call has undefined receiver', 'function f(){"use strict";return this===void 0;}f();');
add('constructor ignores primitive return', 'function C(){this.x=4;return 9;}var o=new C();o.x;');
add('constructor accepts object return', 'function C(){this.x=4;return {x:7};}var o=new C();o.x;');
add('function declaration hoists before call', 'var x=f();function f(){return 9;}x;');
add('variable hoisting shadows outer binding', 'var x=8;function f(){var y=x;var x=3;return y;}f();');
add('last duplicate parameter wins', 'function f(a,a){return a;}f(2,8);');
add('array holes preserve length and absence', 'var a=[,2,,];a.length*100+(0 in a?10:0)+(1 in a?1:0);');
add('signed zero survives numeric equality operations', 'var a=-0;1/a;');
add('number strings and ordered concatenation', '"x"+1+2+":"+(1+2)+":"+(-0);');
add('unknown regex host requirement is explicit', '/a/.test("a");', { expectedStatus: 'unresolved' });
add('fuel exhaustion remains running rather than completing', 'while(true){}', { fuel: 100, expectedStatus: 'fuel-exhausted' });
add('array length grows, then shrink deletes indexed properties', 'var a=[];a[3]=9;var before=a.length;a.length=2;before*100+a.length*10+(3 in a?1:0);');
add('noncanonical numeric property does not change array length', 'var a=[];a["01"]=8;a[1]=7;a.length*100+a["01"]*10+a[1];');
add('argument write updates parameter', 'function f(a){arguments[0]=8;return a;}f(2);');
add('parameter write updates mapped argument', 'function f(a){a=8;return arguments[0];}f(2);');
add('duplicate first parameter is not mapped', 'function f(a,a){arguments[0]=7;return a*100+arguments[0]*10+arguments[1];}f(2,3);');
add('duplicate last parameter is mapped', 'function f(a,a){arguments[1]=8;return a*100+arguments[0]*10+arguments[1];}f(2,3);');
add('deleting argument removes its mapping', 'function f(a){delete arguments[0];a=7;return arguments[0];}f(2);');
add('strict arguments do not alias parameters', 'function f(a){"use strict";arguments[0]=8;return a;}f(2);');
add('for-in puts integer names before insertion-ordered names', 'var o={b:1,2:2,a:3,1:4};var s="";for(var k in o)s+=k;s;');
add('for-in suppresses shadowed prototype properties', 'function C(){}C.prototype={p:1,a:2};var o=new C();o.a=3;o.b=4;var s="";for(var k in o)s+=k;s;');
add('for-in permits value changes without key changes', 'var o={a:1,b:2},s=0;for(var k in o){o.b=5;s+=o[k];}s;');
add('for-in retains complete order across 300 value-only mutations', 'var o={},order="",sum=0;for(var i=299;i>=0;i--)o[i]=i;for(var j=0;j<3;j++)o["s"+j]=j;for(var k in o){o[k]+=1;order+=k+",";sum+=o[k];}order+":"+sum;', { fuel: 300000 });
add('for-in key mutation records unresolved invalidation semantics', 'var o={a:1,b:2};for(var k in o){o.c=3;}1;', { expectedStatus: 'unresolved' });

const standard = (name, source, extra = {}) => add(name, source, { standardLibrary: true, ...extra });
standard('source function toString retains declaration comments and whitespace', 'function /*😀*/ named ( x ) { return x; }named.toString();');
standard('source function toString retains expression CRLF', 'var f=function (y){\r\n/* c */return y;};f.toString();');
standard('source function toString preserves lone UTF16 surrogate in comment', 'function /*\ud800*/ f(){}f.toString();');
standard('source accessor toString retains getter introducer and quoted key', 'var o={get /*before key*/ "x" () { return 1; }};Object.getOwnPropertyDescriptor(o,"x").get.toString();');
standard('source accessor toString retains setter introducer', 'var o={set x(v){this.y=v;}};Object.getOwnPropertyDescriptor(o,"x").set.toString();');
standard('source anonymous function keeps original spelling after inferred name', 'var o={f:function /* comment */ () {}};o.f.toString();');
standard('source function coercion during loader callback comparison', 'var x={loaded:function(){return 7;}};x.loaded!=0;');
standard('source function string conversion does not read changed name', 'function original(x){return x;}Object.defineProperty(original,"name",{get:function(){throw 9;}});original.toString();');
standard('Function toString rejects noncallable receiver', 'try{Function.prototype.toString.call({});}catch(error){error.name;}');
standard('native standard callable toString uses native method spelling', 'Math.max.toString()+":"+Object.keys.toString()+":"+Array.prototype.push.toString();');
standard('Function prototype toString preserves anonymous intrinsic spelling', 'Function.prototype.toString();');
standard('Function prototype toString method reflects itself', 'Function.prototype.toString.toString();');
standard('native callable toString ignores a replacement name getter', 'Object.defineProperty(Math.max,"name",{get:function(){throw 9;}});Math.max.toString();');
standard('RegExp literal exec returns indexed captures and input', 'var r=/(a)(b)?/,m=r.exec("xa");m.index+":"+m.length+":"+m[0]+":"+m[1]+":"+m[2]+":"+m.input+":"+m.groups;');
standard('RegExp global exec updates and resets lastIndex', 'var r=/a/g,s="";s+=r.exec("aba").index+":"+r.lastIndex+":";s+=r.exec("aba").index+":"+r.lastIndex+":";s+=r.exec("aba")+":"+r.lastIndex;s;');
standard('RegExp empty exec does not advance lastIndex', 'var r=/(?:)/g;r.lastIndex=1;var m=r.exec("ab");m.index+":"+r.lastIndex;');
standard('RegExp nonglobal exec coerces lastIndex before ignoring it', 'var s="",r=/a/;r.lastIndex={valueOf:function(){s+="v";return 8;}};r.exec("a")[0]+":"+s+":"+typeof r.lastIndex;');
standard('RegExp lastIndex coercion throw precedes matching', 'var r=/a/;r.lastIndex={valueOf:function(){throw 8;}};try{r.exec("a");}catch(e){e;}');
standard('RegExp nonwritable global lastIndex throws on success', 'var r=/a/g;Object.defineProperty(r,"lastIndex",{writable:false});try{r.exec("a");}catch(e){e.name;}');
standard('RegExp nonwritable global lastIndex throws on miss', 'var r=/a/g;Object.defineProperty(r,"lastIndex",{writable:false});try{r.exec("b");}catch(e){e.name;}');
standard('RegExp nonglobal readonly lastIndex is not written', 'var r=/a/;Object.defineProperty(r,"lastIndex",{value:4,writable:false});r.exec("a")[0]+":"+r.lastIndex;');
standard('RegExp test invokes overridden exec with receiver', 'var r=/a/,s="";r.exec=function(x){s+=x+":"+(this===r);return {};};r.test("b")+":"+s;');
standard('RegExp test exec getter and input conversion order', 'var s="",o={get exec(){s+="e";return function(x){s+="c"+x;return null;};}};var x={toString:function(){s+="s";return "x";}};RegExp.prototype.test.call(o,x)+":"+s;');
standard('RegExp test rejects primitive custom results', 'var r=/a/;r.exec=function(){return 3;};try{r.test("a");}catch(e){e.name;}');
standard('RegExp test falls back when exec is noncallable', 'var r=/a/;r.exec=3;r.test("a");');
standard('RegExp exec brands receiver before input conversion', 'var s="";try{RegExp.prototype.exec.call({}, {toString:function(){s+="s";return "x";}});}catch(e){s+=e.name;}s;');
standard('RegExp constructor call preserves original identity', 'var r=/a/;RegExp(r)===r&&new RegExp(r)!==r;');
standard('RegExp constructor copies flags and resets lastIndex', 'var r=/a/gi;r.lastIndex=3;var s=new RegExp(r);s.source+":"+s.flags+":"+s.lastIndex;');
standard('RegExp constructor changed constructor disables identity shortcut', 'var r=/a/;r.constructor=3;RegExp(r)!==r;');
standard('RegExp constructor converts pattern then flags', 'var s="";var r=new RegExp({toString:function(){s+="p";return "a";}},{toString:function(){s+="f";return "gi";}});s+":"+r.flags;');
standard('RegExp source getter escapes slash and newline', 'new RegExp("a/b\\n").source+":"+new RegExp("").source+":"+new RegExp("[/]").source;');
standard('RegExp source and flag getters are inherited descriptors', 'var r=/a/g,d=Object.getOwnPropertyDescriptor(RegExp.prototype,"source"),l=Object.getOwnPropertyDescriptor(r,"lastIndex");Object.keys(r).length+":"+r.hasOwnProperty("source")+":"+typeof d.get+":"+d.enumerable+":"+d.configurable+":"+l.writable+":"+l.enumerable+":"+l.configurable;');
standard('RegExp prototype getters preserve prototype special cases', 'RegExp.prototype.source+":"+RegExp.prototype.global+":"+RegExp.prototype.flags;');
standard('RegExp flags reads generic properties in order', 'var s="",o={get global(){s+="g";return 1;},get ignoreCase(){s+="i";return 0;},get multiline(){s+="m";return 1;},get dotAll(){s+="s";return 0;},get unicode(){s+="u";return 1;},get sticky(){s+="y";return 1;}};Object.getOwnPropertyDescriptor(RegExp.prototype,"flags").get.call(o)+":"+s;');
standard('RegExp toString is generic and orders property coercion', 'var s="",o={get source(){s+="s";return {toString:function(){s+="S";return "a";}};},get flags(){s+="f";return {toString:function(){s+="F";return "g";}};}};RegExp.prototype.toString.call(o)+":"+s;');
standard('RegExp dynamic unicode and sticky flags work', 'var r=new RegExp(".","uy");r.lastIndex=1;var m=r.exec("😀x");m.index+":"+m[0]+":"+r.lastIndex;');
standard('RegExp rejects malformed constructor syntax', 'try{new RegExp("(");}catch(e){e.name;}');
standard('RegExp unsupported lookbehind stays explicit', 'new RegExp("(?<=a)b");', { expectedStatus: 'unresolved' });
standard('String match returns nonglobal capture metadata', 'var m="xaba".match(/(a)(b)?/);m.join(":")+"/"+m.index+"/"+m.input;');
standard('String global match resets lastIndex and omits captures', 'var r=/(a)(b)?/g;r.lastIndex=2;"aba".match(r).join(":")+"/"+r.lastIndex;');
standard('String global match returns null on no matches', '"abc".match(/z/g);');
standard('String match advances empty Unicode matches by code point', '"😀x".match(new RegExp("(?:)","gu")).length;');
standard('String match advances empty legacy matches by code unit', '"😀x".match(/(?:)/g).length;');
standard('String match converts receiver before reading exec', 'var s="",r=/a/;Object.defineProperty(r,"exec",{get:function(){s+="e";return function(x){s+="c"+x;return null;};}});String.prototype.match.call({toString:function(){s+="s";return "a";}},r);s;');
standard('String global match invokes custom exec repeatedly', 'var n=0,r=/a/g;r.exec=function(){n++;return n<3?{0:"x"}:null;};"a".match(r).join(":")+"/"+n;');
standard('String global match rejects readonly reset of lastIndex', 'var r=/a/g;Object.defineProperty(r,"lastIndex",{writable:false});try{"a".match(r);}catch(e){e.name;}');
standard('String search restores lastIndex including negative zero', 'var r=/b/g;r.lastIndex=-0;var index="abc".search(r);index+":"+(1/r.lastIndex);');
standard('String search preserves previous positive lastIndex', 'var r=/b/g;r.lastIndex=9;"abc".search(r)+":"+r.lastIndex;');
standard('String search custom index is read after restoring lastIndex', 'var r=/b/g;r.lastIndex=8;r.exec=function(){r.lastIndex=7;return {get index(){return r.lastIndex;}};};"abc".search(r)+":"+r.lastIndex;');
standard('String search does not restore lastIndex after callback throw', 'var r=/a/g;r.lastIndex=8;r.exec=function(){r.lastIndex=7;throw 4;};try{"abc".search(r);}catch(e){e+":"+r.lastIndex;}');
standard('String search returns custom index without numeric conversion', 'var r=/a/;r.exec=function(){return {index:"custom"};};"abc".search(r);');
standard('String replacement expands all dollar substitution forms', '"xabcy".replace(/(a)(b)(c)/,"$$|$&|$`|$\'|$1|$2|$3|$10|$99|$0");');
standard('String replacement treats unmatched capture as empty', '"b".replace(/(a)?b/,"[$1]-$10-$2");');
standard('String replacement callback receives captures index and input', '"xab".replace(/(a)(b)?/,function(m,a,b,i,s){return m+":"+a+":"+b+":"+i+":"+s;});');
standard('String replacement callback preserves undefined captures', '"b".replace(/(a)?b/,function(m,a){return typeof a;});');
standard('String replacement collects global matches before callbacks', 'var log="",n=0,r=/a/g;r.exec=function(){log+="e";return n++<2?{0:"a",index:n-1,length:1}:null;};var out="aa".replace(r,function(){log+="c";return {toString:function(){log+="s";return "x";}};});out+":"+log;');
standard('String replacement invokes callbacks for overlapping custom matches', 'var n=0,s="",r=/a/g;r.exec=function(){return n++<2?{0:"aa",index:0,length:1}:null;};var out="aaa".replace(r,function(){s+="c";return "x";});out+":"+s;');
standard('String replacement clamps negative and excessive custom indices', 'var n=0,r=/a/g;r.exec=function(){return n<2?{0:"a",index:n++===0?-3:99,length:1}:null;};"abc".replace(r,"x");');
standard('String replacement string conversion precedes regex execution', 'var s="",r=/a/;r.exec=function(){s+="e";return null;};"a".replace(r,{toString:function(){s+="s";return "x";}});s;');
standard('String replacement empty global Unicode matches advance correctly', '"😀x".replace(new RegExp("(?:)","gu"),"-");');
standard('String replacement string search is literal and first-only', '"a.a.a".replace(".","[$&]");');
standard('String replacement string search callback arguments', '"abcabc".replace("bc",function(m,i,s){return m+":"+i+":"+s;});');
standard('String split string separator preserves empty components', '"a,,b,".split(",").join(":");');
standard('String split empty separator uses UTF16 code units', '"😀x".split("").length;');
standard('String split limit applies uint32 conversion', '"a,b,c".split(",",2).join(":")+"/"+"a,b".split(",",0).length;');
standard('String split regexp includes captures and undefined groups', 'var a="abxb".split(/(a)?b/);a.length+":"+a.join("|")+":"+typeof a[3];');
standard('String split preserves original regexp lastIndex', 'var r=/,/g;r.lastIndex=9;"a,b,c".split(r).join(":")+"/"+r.lastIndex;');
standard('String split Unicode empty expression advances codepoints', '"😀x".split(new RegExp("(?:)","u")).join(":");');
standard('standard Math exact arithmetic and argument order', 'var s="";function f(x){s+=x;return x;}Math.max(f(1),f(2));s+":"+Math.floor(-1.2)+":"+Math.ceil(-1.2)+":"+Math.round(-1.5);');
standard('standard Math min preserves negative zero', '1/Math.min(0,-0);');
standard('standard decimal Number formatting', '(1.25).toFixed(1)+":"+(12345).toPrecision(3)+":"+(1e21).toString();');
standard('standard binary and hexadecimal integer formatting', '(42).toString(2)+":"+(65535).toString(16);');
standard('standard UTF16 char access preserves surrogate units', 'var s="😀";s.length*100000+s.charCodeAt(0);');
standard('standard UTF16 substring indexes code units', '"abc".slice(-2)+":"+"abc".substring(2,0)+":"+"abc".substr(1,1);');
standard('standard string search and ASCII casing', '"AbCd".toLowerCase()+":"+"xy".toUpperCase()+":"+"ababa".indexOf("ba",2);');
standard('standard String.fromCharCode applies uint16 conversion', 'String.fromCharCode(65536+65,-1).charCodeAt(1);');
standard('standard primitive constructors', 'Number(" 12 ")+String(false)+Boolean(0);');
standard('standard primitive boxing', 'new Number(12).valueOf()+new String("ab").length;');
standard('standard global parsers keep prefixes', 'parseInt(" 0x10",0)+parseInt("12px",10)+parseFloat(" -1.5e2rest");');
standard('standard function call uses explicit receiver', 'function f(x){return this.n+x;}f.call({n:3},4);');
standard('standard formatting range error precedes later statements', 'var s="";try{(1).toFixed(101);s+="wrong";}catch(e){s+=e.name;}s;');
standard('standard incompatible Number receiver throws TypeError', 'try{Number.prototype.toFixed.call(null,0);}catch(e){e.name;}');
standard('standard null String receiver throws TypeError', 'try{String.prototype.charAt.call(null,0);}catch(e){e.name;}');
standard('standard object argument coercion remains an explicit requirement', 'var s="";try{(1).toFixed({valueOf:function(){s+="v";return 101;}});}catch(e){s+="c";}s;', { expectedStatus: 'unresolved' });
standard('standard fdlibm Math.pow executes native source exponentiation', 'Math.pow(2,3);');
standard('standard free random remains an explicit request', 'Math.random();', { expectedStatus: 'unresolved' });
standard('Unicode casing uses full Unicode13 mappings', '"éß".toUpperCase()+":"+"ΟΣ ΟΣΑ".toLowerCase()+":"+"𐐀".toLowerCase();');
standard('apply preserves UTF16 input and receiver', 'String.fromCharCode.apply(null,[65,66,55357,56832]);');
standard('apply reads a generic argument object', 'function f(x,y){return this.a+x+y;}f.apply({a:3},{0:4,1:5,length:2});');
standard('apply reads argument length and indexed getters in order', 'var s="";var a={get length(){s+="l";return 2;},get 0(){s+="a";return 4;},get 1(){s+="b";return 5;}};function f(x,y){s+="f";return x+y;}f.apply(null,a);s;');
standard('pop removes last item while preserving an earlier hole', 'var a=[1,,3];var v=a.pop();a.length*100+(1 in a?10:0)+v;');
standard('slice preserves absent elements', 'var a=[1,,3,4].slice(1,3);a.length*100+(0 in a?10:0)+a[1];');
standard('push and join preserve separator and holes', 'var a=[1,,3];a.push(4,5);a.join(":");');
standard('indexOf and lastIndexOf apply negative starts', 'var a=[1,2,1,2];a.indexOf(2,-3)*10+a.lastIndexOf(1,-2);');


standard('splice grows sparse arrays and returns removed holes', 'var a=[1,,3,4],b=a.splice(-3,1,8,9,10);a.length+":"+a.join("|")+":"+b.length+":"+b.join("|")+":"+Object.keys(a).join(",");');
standard('splice shrinking preserves sparse result', 'var a=[1,,3,4],b=a.splice(1,2);a.join(":")+"/"+b.join(":")+"/"+Object.keys(b).join(":");');
standard('splice without arguments changes nothing', 'var a=[1,,3],b=a.splice();a.join(":")+"/"+b.length;');
standard('shift and unshift preserve sparse indices', 'var a=[,2,,4];var x=a.shift();a.unshift(8,9);a.join(":")+"/"+Object.keys(a).join(":")+"/"+x;');
standard('reverse preserves holes and order', 'var a=[1,,3,4,,];a.reverse();a.join(":")+"/"+Object.keys(a).join(":");');
standard('native array sort orders numeric strings', '[3,1,2].sort().join(":");');
standard('URI conversion uses string hint and source method order', 'var s="";var value={toString:function(){s+="s";return {};},valueOf:function(){s+="v";return "é a";}};encodeURIComponent(value)+":"+s;');
standard('URI conversion callback throw is preserved', 'try{encodeURI({toString:function(){throw 7;}});}catch(e){e;}');
standard('URI lone surrogate throws after source conversion', 'var s="";try{encodeURIComponent({toString:function(){s+="s";return "\\ud800";}});}catch(e){s+=e.name;}s;');
standard('URI reserved escapes differ between decode functions', 'decodeURI("%3B%2F%3F%3A%40%26%3D%2B%24%2C%23")+":"+decodeURIComponent("%3B%2F%3F%3A%40%26%3D%2B%24%2C%23");');
standard('URI astral text roundtrip preserves UTF16', 'decodeURIComponent(encodeURIComponent("é😀𐐀"));');
standard('URI malformed byte sequence throws URIError', 'try{decodeURIComponent("%C0%AF");}catch(e){e.name;}');
standard('legacy escape and unescape preserve surrogate units', 'unescape(escape("é😀\\ud800"));');
standard('legacy escape uses source string conversion first', 'var s="";escape({toString:function(){s+="s";return "é ";}})+":"+s;');
standard('Object.keys sorts integer keys and omits nonenumerable keys', 'var o={b:1,2:2,a:3,1:4};Object.defineProperty(o,"hidden",{value:9});Object.keys(o).join(":");');
standard('Object.getOwnPropertyNames includes nonenumerable and string virtual properties', 'Object.getOwnPropertyNames("ab").join(":");');
standard('Object.create preserves requested prototype and own-key distinctions', 'var p={x:1};var o=Object.create(p);o.y=2;Object.getPrototypeOf(o)===p&&o.hasOwnProperty("y")&&!o.hasOwnProperty("x")&&o.propertyIsEnumerable("y");');
standard('Object.create null prototype has no inherited members', 'var o=Object.create(null);o.x=1;Object.getPrototypeOf(o)===null&&!("toString" in o);');
standard('Object descriptor defaults are false and preserve existing fields', 'var o={};Object.defineProperty(o,"x",{value:7});Object.defineProperty(o,"x",{});var d=Object.getOwnPropertyDescriptor(o,"x");d.value+":"+d.writable+":"+d.enumerable+":"+d.configurable;');
standard('Object descriptor getters execute in required order', 'var log="",o={};var d={get enumerable(){log+="e";return true;},get configurable(){log+="c";return true;},get value(){log+="v";return 7;},get writable(){log+="w";return true;},get get(){log+="g";return void 0;},get set(){log+="s";return void 0;}};try{Object.defineProperty(o,"x",d);}catch(e){log+=e.name;}log+":"+("x" in o);');
standard('Object descriptor invalid getter stops before reading setter', 'var log="",o={};var d={get get(){log+="g";return 3;},get set(){log+="s";return void 0;}};try{Object.defineProperty(o,"x",d);}catch(e){log+=e.name;}log;');
standard('Object descriptor getter throw propagates before definition', 'var o={};try{Object.defineProperty(o,"x",{get value(){throw 8;}});}catch(e){e+("x" in o?10:0);}');
standard('Object.defineProperty invokes assigned accessors', 'var n=2,o={};Object.defineProperty(o,"x",{get:function(){return n+1;},set:function(v){n=v*2;},configurable:true});o.x=4;o.x;');
standard('Object.getOwnPropertyDescriptor does not invoke the property getter', 'var n=0,o={get x(){n++;return 3;}};var d=Object.getOwnPropertyDescriptor(o,"x");typeof d.get+":"+n;');
standard('nonconfigurable properties use SameValue for NaN', 'var o={};Object.defineProperty(o,"x",{value:NaN});Object.defineProperty(o,"x",{value:NaN});isNaN(o.x);');
standard('nonconfigurable properties distinguish signed zero', 'var o={};Object.defineProperty(o,"x",{value:0});try{Object.defineProperty(o,"x",{value:-0});}catch(e){e.name;}');
standard('nonconfigurable descriptor kind cannot change', 'var o={};Object.defineProperty(o,"x",{value:7});try{Object.defineProperty(o,"x",{get:function(){return 3;}});}catch(e){e.name;}');
standard('preventExtensions preserves existing writes but rejects new definitions', 'var o={x:1};Object.preventExtensions(o);o.x=2;var s="";try{Object.defineProperty(o,"y",{value:3});}catch(e){s=e.name;}s+":"+o.x+":"+Object.isExtensible(o);');
standard('defining an array index extends its length', 'var a=[];Object.defineProperty(a,"3",{value:8});a.length*10+a[3];');
standard('defining array length shrinks and sets writability', 'var a=[1,2,3];Object.defineProperty(a,"length",{value:1,writable:false});a[2]=7;a.length*100+(2 in a?10:0)+Object.getOwnPropertyDescriptor(a,"length").writable;');
standard('failed array shrink retains partial deletions and requested readonly length', 'var a=[1,2,3,4];Object.defineProperty(a,"1",{configurable:false});var s="";try{Object.defineProperty(a,"length",{value:0,writable:false});}catch(e){s=e.name;}s+":"+a.length+":"+(3 in a)+":"+Object.getOwnPropertyDescriptor(a,"length").writable;');
standard('mapped argument descriptor reads the current parameter value', 'function f(a){a=8;return Object.getOwnPropertyDescriptor(arguments,"0").value;}f(2);');
standard('readonly argument descriptor breaks parameter mapping', 'function f(a){Object.defineProperty(arguments,"0",{writable:false});a=8;return arguments[0];}f(2);');
standard('argument value descriptor updates mapped parameter', 'function f(a){Object.defineProperty(arguments,"0",{value:8});return a;}f(2);');
standard('Object prototype methods handle primitives and null', 'Object.prototype.toString.call(null)+":"+Object.prototype.toString.call(void 0)+":"+Object.prototype.hasOwnProperty.call("ab","0");');
standard('ToPrimitive tries valueOf then toString and preserves source effects', 'var log="";var o={valueOf:function(){log+="v";return {};},toString:function(){log+="s";return "7";}};var n=o-2;log+":"+n;');
standard('ToPrimitive gets each method before calling it', 'var log="";var o={get valueOf(){log+="g";return function(){log+="v";return {};};},get toString(){log+="h";return function(){log+="s";return "4";};}};var n=o*2;log+":"+n;');
standard('ToPrimitive callback throws before later callbacks', 'var log="";var o={valueOf:function(){log+="v";throw 7;},toString:function(){log+="s";return "4";}};try{o*2;}catch(e){log+=e;}log;');
standard('object property keys use string hint before indexing', 'var log="";var k={toString:function(){log+="s";return "x";},valueOf:function(){log+="v";return 1;}};var o={x:8};o[k]+":"+log;');
standard('postfix object update calls valueOf and returns old number', 'var n=0;var x={valueOf:function(){n++;return 4;}};var before=x++;n*100+before*10+x;');
standard('nested arrays convert through join source operations', '[1,[2,3],null].join(":");');
standard('map preserves holes and receives source index', '[1,,3].map(function(v,i){return v+i;}).join(":");');
standard('filter compacts passing elements', '[1,,2,3,4].filter(function(v){return v%2;}).join(":");');
standard('forEach skips holes and receives original receiver', 'var a=[1,,3],s="";a.forEach(function(v,i,o){s+=v+":"+i+":"+(o===a)+";";});s;');
standard('some short circuits callback traversal', 'var s="";var v=[1,2,3].some(function(v){s+=v;return v===2;});s+":"+v;');
standard('every short circuits callback traversal', 'var s="";var v=[1,2,3].every(function(v){s+=v;return v<2;});s+":"+v;');
standard('reduce follows left direction and skips holes', '[1,,3,4].reduce(function(a,b){return a-b;});');
standard('reduceRight follows right direction and skips holes', '[1,,3,4].reduceRight(function(a,b){return a-b;});');
standard('empty reduce without initial value throws', 'try{[].reduce(function(a,b){return a+b;});}catch(e){e.name;}');
standard('empty reduce with initial value returns it', '[].reduce(function(a,b){return a+b;},7);');
standard('concat spreads arrays while preserving holes', '[1,,3].concat([4,,6],7).join(":");');

let sourceHash = null;
let sourceCases = 0;
if (process.argv.includes('--engine')) {
  const source = loadGameSource(); const ast = compilePinnedGameAst();
  sourceHash = source.hashes['main.js'];
  const assignment = name => {
    const node = ast.nodes.find(n => n.kind === 'expr' && n.tag === 'assignment' && n.operator === 'assign'
      && ast.nodes[n.left]?.tag === 'member' && !ast.nodes[n.left].computed
      && ast.nodes[ast.nodes[n.left].object]?.name === 'Game'
      && ast.nodes[ast.nodes[n.left].property]?.name === name
      && ast.nodes[n.right]?.tag === 'function');
    assert(node, `Missing pinned Game.${name} assignment`);
    assert.equal(ast.units[node.source.unit].name, 'main.js');
    return source.sources['main.js'].slice(node.source.start, node.source.end) + ';';
  };
  const declaration = name => {
    const node = ast.nodes.find(n => n.kind === 'stmt' && n.tag === 'functionDeclaration' && n.name === name);
    assert(node, `Missing pinned function ${name}`);
    return source.sources['main.js'].slice(node.source.start, node.source.end);
  };
  for (const input of ['', 'cookie', 'é', '😀𐐀', 'a\0b', '\ud800']) {
    standard(`native utf8_to_b64(${JSON.stringify(input)})`, `${declaration('utf8_to_b64')}utf8_to_b64(${JSON.stringify(input)});`, { browserExpected: true });
    sourceCases++;
  }
  for (const input of ['', 'Y29va2ll', 'w6k=', '8J+YgPCQkIA=', 'YQBi', 'wA==', 'not base64!']) {
    standard(`native b64_to_utf8(${JSON.stringify(input)})`, `${declaration('b64_to_utf8')}b64_to_utf8(${JSON.stringify(input)});`, { browserExpected: true });
    sourceCases++;
  }
  for (const input of ['cookie', 'é😀𐐀', 'a\0b']) {
    standard(`native UTF8 save helper roundtrip ${JSON.stringify(input)}`, `${declaration('utf8_to_b64')}${declaration('b64_to_utf8')}b64_to_utf8(utf8_to_b64(${JSON.stringify(input)}));`, { browserExpected: true });
    sourceCases++;
  }
  for (const value of ['a.*?[]{}()^$|-/\\', 'plain', 'é😀', '']) {
    standard(`native escapeRegExp(${JSON.stringify(value)})`, `${declaration('escapeRegExp')}escapeRegExp(${JSON.stringify(value)});`);
    sourceCases++;
  }
  for (const [find, replacement, input] of [['.', '$&!', 'a.b.c'], ['a', '$$', 'aba'], ['', '-', 'ab'], ['[x]', 'y', '[x][x]'], ['😀', 'x', '😀a😀']]) {
    standard(`native replaceAll(${JSON.stringify([find, replacement, input])})`, `${declaration('escapeRegExp')}${declaration('replaceAll')}replaceAll(${JSON.stringify(find)},${JSON.stringify(replacement)},${JSON.stringify(input)});`);
    sourceCases++;
  }
  for (const value of [0, 1, 4, 9, 42, 1999, 4000]) {
    standard(`native romanize(${value})`, `${declaration('romanize')}romanize(${value});`);
    sourceCases++;
  }
  const formatterStart = ast.nodes.find(n => n.kind === 'stmt' && n.tag === 'functionDeclaration' && n.name === 'formatEveryThirdPower');
  const formatterEnd = ast.nodes.find(n => n.kind === 'stmt' && n.tag === 'functionDeclaration' && n.name === 'BeautifyInText');
  assert(formatterStart && formatterEnd, 'Missing pinned formatting span');
  assert.equal(ast.units[formatterStart.source.unit].name, 'main.js');
  assert.equal(ast.units[formatterEnd.source.unit].name, 'main.js');
  // Exact contiguous pinned source, including formatter tables and setup loops.
  // Game.prefs is an explicit comparison input, not a stand-in callback.
  const formatterSource = source.sources['main.js'].slice(formatterStart.source.start, formatterEnd.source.end);
  for (const format of [0, 1]) {
    for (const value of ['0', '12.345', '-12.345', '1000000', '1e15', '1e50', 'Infinity']) {
      standard(`native Beautify(${value}) format=${format}`, `var Game={prefs:{format:${format}}};${formatterSource}Beautify(${value},2);`, { fuel: 1000000 });
      sourceCases++;
    }
    for (const input of ['Bake 1000000 cookies.', '1,234,567 cookies and 42 grandmas', 'No numbers here']) {
      standard(`native BeautifyInText format=${format} ${JSON.stringify(input)}`, `var Game={prefs:{format:${format}}};${formatterSource}BeautifyInText(${JSON.stringify(input)});`, { fuel: 1000000 });
      sourceCases++;
    }
  }
  for (const value of ['cookie', '', 'abc DEF']) {
    standard(`native cap(${JSON.stringify(value)})`, `${declaration('cap')}cap(${JSON.stringify(value)});`);
    sourceCases++;
  }
  for (const draw of [0, 0.5, 0.999]) {
    // Deterministic comparison input only. This synthetic Math binding is not
    // an admissible game action or a strategy that controls random outcomes.
    standard(`native choose with explicit fixed draw ${draw}`, `${declaration('choose')}Math.random=function(){return ${draw};};choose([10,20,30]);`);
    sourceCases++;
    for (const value of [-1.25, 0, 1.25]) {
      standard(`native randomFloor(${value}) with explicit fixed draw ${draw}`, `${declaration('randomFloor')}Math.random=function(){return ${draw};};randomFloor(${value});`);
      sourceCases++;
    }
  }
  for (const mode of [0, 1]) for (const entry of [null, { bought: 0, unlocked: 1, pool: 'cookie' }, { bought: 1, unlocked: 1, pool: 'cookie' }, { bought: 1, unlocked: 1, pool: 'prestige' }, { bought: 1, unlocked: 1, tier: 'fortune' }]) {
    const state = { ascensionMode: mode, Upgrades: entry ? { target: entry } : {} };
    add(`native Game.Has mode=${mode} entry=${JSON.stringify(entry)}`, `var Game=${JSON.stringify(state)};${assignment('Has')}Game.Has("target");`);
    add(`native Game.HasUnlocked mode=${mode} entry=${JSON.stringify(entry)}`, `var Game=${JSON.stringify(state)};${assignment('HasUnlocked')}Game.HasUnlocked("target");`);
    sourceCases += 2;
  }
  for (const entry of [null, { won: 0 }, { won: 1 }]) {
    add(`native Game.HasAchiev ${JSON.stringify(entry)}`, `var Game=${JSON.stringify({ Achievements: entry ? { target: entry } : {} })};${assignment('HasAchiev')}Game.HasAchiev("target");`);
    sourceCases++;
  }
  for (const level of [5, 6, 27]) for (const slots of [[0, 0], [1, 0], [2, 0], [1, 2], [2, 2]]) {
    const state = { dragonLevel: level, dragonAura: slots[0], dragonAura2: slots[1], dragonAuras: [{ name: 'none' }, { name: 'Target' }, { name: 'Reality Bending' }], dragonAurasBN: { Target: { id: 2 } } };
    add(`native Game.auraMult ${level}/${slots}`, `var Game=${JSON.stringify(state)};${assignment('auraMult')}Game.auraMult("Target");`);
    sourceCases++;
  }
}
const encode = value => {
  if (value === undefined) return { type: 'undefined' };
  if (value === null) return { type: 'null' };
  if (typeof value === 'number') return { type: 'number', bits: numberLiteralBits(value) };
  if (typeof value === 'boolean') return { type: 'boolean', value };
  if (typeof value === 'string') return { type: 'string', units: Array.from({ length: value.length }, (_, i) => value.charCodeAt(i)) };
  throw new Error('Comparison fixture must return a primitive value');
};
const request = cases.map(c => ({ ast: compileJavaScript(c.source, { name: c.name }), fuel: c.fuel, standardLibrary: !!c.standardLibrary }));
const executable = fileURLToPath(new URL('./.lake/build/bin/jsastcheck', import.meta.url));
const result = spawnSync(executable, ['--execute'], { input: JSON.stringify(request), encoding: 'utf8', timeout: 60000, maxBuffer: 1024 * 1024 });
if (result.error) throw result.error;
assert.equal(result.status, 0, result.stderr);
const outputs = JSON.parse(result.stdout); assert.equal(outputs.length, cases.length);
let nativeEngine = null;
let nativeExpected = null;
if (process.argv.includes('--engine')) {
  nativeEngine = inspectNativeEngine();
  nativeExpected = runNativeEngine(`
    const fs=require('fs'),vm=require('vm');
    const encode=value=>{
      if(value===undefined)return {type:'undefined'};
      if(value===null)return {type:'null'};
      if(typeof value==='number'){const b=Buffer.alloc(8);b.writeDoubleBE(value);return {type:'number',bits:b.readBigUInt64BE().toString()};}
      if(typeof value==='boolean')return {type:'boolean',value};
      if(typeof value==='string')return {type:'string',units:Array.from({length:value.length},(_,i)=>value.charCodeAt(i))};
      throw Error('Native comparison fixture must return a primitive');
    };
    const outputs=JSON.parse(fs.readFileSync(0,'utf8')).map(c=>{
      if(c.skip)return null;
      try{return {status:'complete',value:encode(vm.runInNewContext(c.source,{},{timeout:1000}))};}
      catch(cause){return {status:'throw',value:encode(cause)};}
    });process.stdout.write(JSON.stringify(outputs));`, cases.map(c => ({ source: c.source, skip: !!c.expectedStatus || !!c.browserExpected })));
}
let browserEngine = null;
const browserExpected = new Map();
if (process.argv.includes('--engine')) {
  const selected = cases.map((value, index) => ({ ...value, index })).filter(c => c.browserExpected && !c.expectedStatus);
  if (selected.length) {
    const evaluate = function (entries) {
      const encode = value => {
        if (value === undefined) return { type: 'undefined' };
        if (value === null) return { type: 'null' };
        if (typeof value === 'boolean') return { type: 'boolean', value };
        if (typeof value === 'string') return { type: 'string', units: Array.from({ length: value.length }, (_, i) => value.charCodeAt(i)) };
        if (typeof value === 'number') { const view = new DataView(new ArrayBuffer(8)); view.setFloat64(0, value, false); return { type: 'number', bits: view.getBigUint64(0, false).toString() }; }
        throw new Error('Browser fixture must return a primitive');
      };
      return entries.map(entry => {
        // Each direct eval has a fresh local variable/function environment.
        const run = function (source) { return eval(source); };
        try { return { index: entry.index, expected: { status: 'complete', value: encode(run(entry.source)) } }; }
        catch (cause) { return { index: entry.index, expected: { status: 'throw', value: encode(cause) } }; }
      });
    };
    const report = runNativeBrowser(evaluate.toString(), selected.map(c => ({ source: c.source, index: c.index })), { allowEval: true });
    browserEngine = { versions: report.versions, renderer: report.renderer, executableHash: report.executableHash,
      gameEntryPointExecuted: report.gameEntryPointExecuted, externalNetworking: report.externalNetworking };
    for (const entry of report.result) browserExpected.set(entry.index, entry.expected);
  }
}
const failures = [];
for (let i = 0; i < cases.length; i++) {
  const c = cases[i]; const actual = outputs[i];
  try {
    if (c.expectedStatus) assert.equal(actual.status, c.expectedStatus);
    else {
      let expected = browserExpected.get(i) || nativeExpected?.[i];
      if (!expected) {
        const context = c.browserExpected ? { btoa: globalThis.btoa, atob: globalThis.atob } : {};
        try { expected = { status: 'complete', value: encode(vm.runInNewContext(c.source, context, { timeout: 1000 })) }; }
        catch (cause) { expected = { status: 'throw', value: encode(cause) }; }
      }
      assert.deepEqual({ status: actual.status, value: actual.value }, expected);
    }
    assert.equal(actual.javascriptSemanticsVerified, false);
  } catch (error) { failures.push({ name: c.name, actual, message: error.message }); }
}
if (failures.length) {
  console.error(JSON.stringify(failures, null, 2));
  process.exitCode = 1;
}
console.log(JSON.stringify({ cases: cases.length, passed: cases.length - failures.length, sourceCases, sourceHash,
  comparisonEngine: nativeEngine || { versions: process.versions, arch: process.arch, platform: process.platform, label: 'Host Node; not the installed game engine' }, browserEngine, javascriptSemanticsVerified: false }));

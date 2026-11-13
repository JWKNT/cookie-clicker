/** Finite source/DOM comparisons, not full browser refinement or game optimality. */
import assert from 'node:assert/strict';
import { spawnSyncWithFileInput as spawnSync } from './process-input.mjs';
import { fileURLToPath } from 'node:url';
import { readFileSync } from 'node:fs';
import { compileJavaScript } from '../model/javascript-ast.mjs';
import { runNativeBrowser } from '../model/native-browser.mjs';
import { loadGameSource } from '../model/game-source.mjs';

const cases = [];
const add = (name, source, extra = {}) => cases.push({ name, source, ...extra });
const units = text => Array.from({ length: text.length }, (_, index) => text.charCodeAt(index));
add('captured native document method toString uses exact source text', 'document.createElement.toString();');
add('captured native accessor toString retains getter spelling', 'Object.getOwnPropertyDescriptor(Document.prototype,"title").get.toString();');
add('captured native Image constructor toString uses exact spelling', 'Image.toString();');
add('native callable toString ignores mutable name accessors', 'var f=document.createElement;Object.defineProperty(f,"name",{get:function(){throw 9;},configurable:true});f.toString();');
add('native callable aliases retain identical source strings', 'DOMTokenList.prototype.forEach.toString()+":"+Array.prototype.forEach.toString();');
add('created element normalizes attributes and class/id properties', 'var e=document.createElement("DIV");e.setAttribute("ID","a");e.className="x y";e.tagName+":"+e.id+":"+e.getAttribute("class")+":"+e.getAttribute("missing");');
add('prototype source method receives native element', 'Element.prototype.auditMethod=function(){return this.tagName;};document.createElement("span").auditMethod();');
add('textContent excludes comments but retains text-node order', 'var e=document.createElement("div");e.appendChild(document.createTextNode("a"));e.appendChild(document.createComment("hidden"));e.appendChild(document.createTextNode("b"));e.textContent;');
add('append moves the existing node and updates its parent', 'var a=document.createElement("div"),b=document.createElement("div"),x=document.createElement("span");a.appendChild(x);b.appendChild(x);(a.firstChild===null)+":"+(b.firstChild===x)+":"+(x.parentNode===b);');
add('insertBefore node itself preserves sibling position', 'var e=document.createElement("div"),a=document.createTextNode("a"),b=document.createTextNode("b");e.appendChild(a);e.appendChild(b);e.insertBefore(a,a);e.textContent;');
add('insertBefore moves within one parent', 'var e=document.createElement("div"),a=document.createTextNode("a"),b=document.createTextNode("b"),c=document.createTextNode("c");e.appendChild(a);e.appendChild(b);e.appendChild(c);e.insertBefore(c,a);e.textContent;');
add('removeChild rejects a node of another parent', 'var e=document.createElement("div"),x=document.createElement("b");try{e.removeChild(x);}catch(error){error.name;}');
add('removal detaches parent pointer and preserves return identity', 'var e=document.createElement("div"),x=document.createElement("b");e.appendChild(x);(e.removeChild(x)===x)+":"+(x.parentNode===null);');
add('ancestor insertion rejects a cycle', 'var a=document.createElement("div"),b=document.createElement("b");a.appendChild(b);try{b.appendChild(a);}catch(error){error.name;}');
add('innerHTML builds nested text, comments, attrs and parent links', 'var e=document.createElement("div");e.innerHTML="<span id=x>A&amp;B<!--c--><b>C</b></span>";e.textContent+":"+e.firstChild.id+":"+(e.firstChild.parentNode===e)+":"+e.firstChild.lastChild.tagName;');
add('innerHTML replacement detaches prior child', 'var e=document.createElement("div");e.innerHTML="<b>x</b>";var old=e.firstChild;e.innerHTML="<i>y</i>";(old.parentNode===null)+":"+e.firstChild.tagName;');
add('textContent replacement detaches prior child', 'var e=document.createElement("div"),x=document.createElement("span");e.appendChild(x);e.textContent="abc";(x.parentNode===null)+":"+e.firstChild.nodeType+":"+e.textContent;');
for (const name of ['textContent','innerHTML']) for (const expression of ['null','undefined','{toString:function(){return null;}}','{toString:function(){return undefined;}}']) {
  add(`${name} distinguishes direct nullish input from converted ${expression}`, `var e=document.createElement("div");e.textContent="old";e.${name}=${expression};e.textContent+":"+e.innerHTML;`);
}
for (const expression of ['null','undefined','{toString:function(){return null;}}','{toString:function(){return undefined;}}']) {
  add(`image crossOrigin preserves nullable conversion ${expression}`, `var e=document.createElement("img");e.crossOrigin=${expression};e.crossOrigin+":"+e.getAttribute("crossorigin");`);
}
for (const value of ['', 'AUTO', 'metadata', 'none', 'invalid']) {
  add(`audio preload enumerated reflection ${JSON.stringify(value)}`, `var e=document.createElement("audio");var before=e.preload;e.preload=${JSON.stringify(value)};before+":"+e.preload+":"+e.getAttribute("preload");`);
}
for (const [tag,value] of [['input',''],['input','BUTTON'],['input','invalid'],['button',''],['button','RESET'],['button','invalid'],['select','ignored'],['textarea','ignored']]) {
  add(`${tag} native type reflection with ${JSON.stringify(value)}`, `var e=document.createElement(${JSON.stringify(tag)});var before=e.type;e.setAttribute("type",${JSON.stringify(value)});before+":"+e.type;`);
}
add('select type responds to multiple attribute', 'var e=document.createElement("select");e.setAttribute("multiple","");e.type;');
add('native media getter rejects an unrelated element receiver', 'try{Object.getOwnPropertyDescriptor(HTMLMediaElement.prototype,"preload").get.call(document.createElement("div"));}catch(e){e.name;}');
add('setAttribute converts name then value through source callbacks', 'var s="",e=document.createElement("div");e.setAttribute({toString:function(){s+="n";return "DATA-X";}},{toString:function(){s+="v";return "value";}});s+":"+e.getAttribute("data-x");');
add('setAttribute converts both arguments before invalid name validation', 'var s="",e=document.createElement("div");try{e.setAttribute({toString:function(){s+="n";return "bad name";}},{toString:function(){s+="v";return "value";}});}catch(error){s+=error.name;}s;');
add('setAttribute propagates value conversion throw before name validation', 'var s="",e=document.createElement("div");try{e.setAttribute("bad name",{toString:function(){s+="v";throw 7;}});}catch(error){s+=error;}s;');
add('borrowed Element method rejects Document before name coercion', 'var s="";try{Element.prototype.setAttribute.call(document,{toString:function(){s+="n";return "x";}},{toString:function(){s+="v";return "y";}});}catch(error){s+=error.name;}s;');
add('borrowed Document method rejects Element before name coercion', 'var s="";try{Document.prototype.createElement.call(document.createElement("div"),{toString:function(){s+="n";return "b";}});}catch(error){s+=error.name;}s;');
add('borrowed Element method rejects Text before name coercion', 'var s="";try{Element.prototype.getAttribute.call(document.createTextNode("x"),{toString:function(){s+="n";return "id";}});}catch(error){s+=error.name;}s;');
add('missing setAttribute value rejects before name coercion', 'var s="",e=document.createElement("div");try{e.setAttribute({toString:function(){s+="n";return "id";}});}catch(error){s+=error.name;}s;');
add('missing required DOM arguments throw TypeError', 'var s="",e=document.createElement("div");try{document.createElement();}catch(error){s+=error.name;}try{e.getElementsByTagName();}catch(error){s+=":"+error.name;}try{e.appendChild();}catch(error){s+=":"+error.name;}s;');
add('createElement converts its name through source methods', 'var s="";document.createElement({toString:function(){s+="s";return "SPAN";}}).tagName+":"+s;');
add('createElement rejects invalid name', 'try{document.createElement("bad name");}catch(error){error.name;}');
add('tag collection stays live after append and removal', 'var e=document.createElement("div"),c=e.getElementsByTagName("span"),x=document.createElement("span");var s=""+c.length;e.appendChild(x);s+=":"+c.length+":"+(c[0]===x);e.removeChild(x);s+":"+c.length+":"+c.item(0);');
add('tag collection item and namedItem preserve object identity', 'var e=document.createElement("div");e.innerHTML="<span id=a></span><b></b><span name=b></span>";var c=e.getElementsByTagName("span");c.length+":"+(c.item(0)===c.namedItem("a"))+":"+(c.item(1)===c.namedItem("b"))+":"+c.item(9);');
add('collection namedItem numeric string searches names rather than indices', 'var e=document.createElement("div");e.innerHTML="<span id=a></span><span id=0></span>";var c=e.getElementsByTagName("span");(c.namedItem("0")===c.item(1))+":"+(c.namedItem("1")===null)+":"+(c[0]===c.item(0));');
add('class collection reevaluates class mutations', 'var e=document.createElement("div"),x=document.createElement("b");e.appendChild(x);var c=e.getElementsByClassName("a b"),s=""+c.length;x.className="a b c";s+=":"+c.length;x.className="a";s+":"+c.length;');
add('collection includes descendants but not its root', 'var e=document.createElement("div");e.innerHTML="<div><div></div></div>";e.getElementsByTagName("div").length;');
add('collection reflects innerHTML replacement', 'var e=document.createElement("div");e.innerHTML="<b id=old>x</b>";var c=e.getElementsByTagName("b"),old=c.item(0);e.innerHTML="<b id=new>y</b><b>z</b>";c.length+":"+c.item(0).id+":"+(old.parentNode===null);');
add('childNodes includes text comments and elements in exact order', 'var e=document.createElement("div");e.innerHTML="a<!--b--><span>c</span>";var n=e.childNodes;n.length+":"+n[0].nodeType+":"+n[1].nodeType+":"+n[2].nodeType+":"+(n instanceof NodeList);');
add('childNodes preserves SameObject while the child set changes', 'var e=document.createElement("div"),n=e.childNodes;var first=n.length;e.appendChild(document.createTextNode("a"));var middle=n.length;e.removeChild(e.firstChild);first+":"+middle+":"+n.length+":"+(n===e.childNodes);');
add('childNodes reflects replacement and keeps old node detached', 'var e=document.createElement("div");e.innerHTML="<b>old</b>";var n=e.childNodes,old=n[0];e.innerHTML="new<!--comment-->";n.length+":"+n[0].nodeType+":"+(old.parentNode===null);');
add('text and comment nodes expose live empty childNodes objects', 'var a=document.createTextNode("x"),b=document.createComment("y");a.childNodes.length+":"+b.childNodes.length+":"+(a.childNodes===a.childNodes);');
add('NodeList item converts indices and distinguishes indexed absence', 'var e=document.createElement("div"),s="";e.appendChild(document.createTextNode("a"));var n=e.childNodes;n.item({valueOf:function(){s+="v";return 0;}}).nodeType+":"+s+":"+n.item(-1)+":"+n[3]+":"+(0 in n)+":"+(1 in n)+":"+n["00"];');
add('NodeList item requires an argument and brands before conversion', 'var n=document.createElement("div").childNodes,s="";try{n.item();}catch(e){s+=e.name;}try{NodeList.prototype.item.call({}, {valueOf:function(){s+="wrong";return 0;}});}catch(e){s+=":"+e.name;}s;');
add('NodeList forEach is the generic native Array alias', '(NodeList.prototype.forEach===Array.prototype.forEach)+":"+(function(){var s="";NodeList.prototype.forEach.call({0:"x",length:1},function(x){s+=x;});return s;})();');
add('NodeList forEach reads live child positions after removal', 'var e=document.createElement("div"),s="";e.innerHTML="a<!--b--><span>c</span>";e.childNodes.forEach(function(node,index){s+=node.nodeType;if(index===0)e.removeChild(node);});s;');
add('NodeList forEach captures initial length before appended children', 'var e=document.createElement("div"),s="";e.innerHTML="a<b>b</b>";e.childNodes.forEach(function(node,index){s+=node.nodeType;if(index===0)e.appendChild(document.createComment("last"));});s+":"+e.childNodes.length;');
add('readonly NodeList index mutation remains explicit', 'var e=document.createElement("div");e.appendChild(document.createTextNode("a"));e.childNodes[0]=document.createTextNode("b");', {expectedStatus:'unresolved'});
add('native source childNodes nodeValue assignment updates the actual text node', 'var e=document.createElement("div");e.innerHTML="old <b>child</b>";e.childNodes[0].nodeValue="new ";e.textContent;');
for(const expression of ['null','undefined','{toString:function(){return null;}}','{toString:function(){return undefined;}}']){
  add(`nodeValue nullable conversion ${expression}`, `var e=document.createTextNode("old");e.nodeValue=${expression};e.nodeValue+":"+e.textContent;`);
}
add('nodeValue element setter converts input before ignoring its string', 'var e=document.createElement("div"),s="";e.nodeValue={toString:function(){s+="s";return "ignored";}};s+":"+e.nodeValue;');
add('nodeValue setter changes comment data without changing element text', 'var e=document.createElement("div"),c=document.createComment("old");e.appendChild(c);c.nodeValue="new";e.innerHTML+":"+e.textContent;');
add('innerHTML serializes escaped text and attributes', 'var e=document.createElement("div"),x=document.createElement("span");x.setAttribute("data-x",\'a"&<> \');x.textContent="&<> ";e.appendChild(x);e.innerHTML;');
add('innerHTML serializes void tags and comments', 'var e=document.createElement("div");e.innerHTML="<input disabled><br><!--c--><span>x</span>";e.innerHTML;');
add('innerHTML rawtext serialization leaves style text intact', 'var e=document.createElement("div"),s=document.createElement("style");s.textContent="a{content:\'<b>&\'}";e.appendChild(s);e.innerHTML;');
add('innerHTML RCDATA serialization escapes text', 'var e=document.createElement("div"),s=document.createElement("textarea");s.textContent="<b>&\\n";e.appendChild(s);e.innerHTML;');
add('clearTimeout removes queued source callback', 'var id=setTimeout(function(){throw 99;},0);clearTimeout(id);typeof id;', { timerCount: 0 });
add('timer callback registration is explicit without autoevents', 'var x=0;setTimeout(function(){x=1;},0);x;', { timerCount: 1 });
add('unseeded draw consumes the supplied diagnostic uniform53 index', 'Math.random();', { randomInputs: [4503599627370496], randomInputsRemaining: 0 });
add('missing entropy remains an explicit model request', 'Math.random();', { expectedStatus: 'unresolved' });
add('layout has no guessed zero rectangle', 'document.createElement("div").getBoundingClientRect().width;', { expectedStatus: 'unresolved' });
add('unsupported document insertion validation remains explicit', 'document.appendChild(document.createElement("body"));', { expectedStatus: 'unresolved' });
const initialHtml = '<!doctype html><html><head><title>fixture</title></head><body><div id=a>A&amp;B<!--c--></div><script>throw 99;</script></body></html>';
add('document title getter collapses HTML whitespace', 'document.title="  A\\t B\\n\\r C\\f ";document.title;', { initialHtml });
add('document title setter performs source string conversion', 'var s="";document.title={toString:function(){s+="s";return "new title";}};s+":"+document.title;', { initialHtml });
add('document title creates missing head title element', 'document.title="new title";document.head.lastChild.tagName+":"+document.title;', { initialHtml: '<!doctype html><html><head></head><body></body></html>' });
add('document title without title or head leaves document unchanged', 'document.documentElement.removeChild(document.head);document.title="ignored";document.title+":"+document.getElementsByTagName("title").length;', { initialHtml: '<!doctype html><html><head></head><body></body></html>' });
add('document title uses first HTML title even in body', 'var t=document.createElement("title");t.text="body title";document.body.appendChild(t);document.title="changed";document.title+":"+t.text+":"+document.head.getElementsByTagName("title").length;', { initialHtml: '<!doctype html><html><head></head><body></body></html>' });
add('title text excludes text inside child elements', 'var t=document.getElementsByTagName("title")[0],b=document.createElement("b");b.textContent="nested";t.appendChild(b);t.appendChild(document.createTextNode("tail"));t.text+":"+document.title;', { initialHtml });
add('setting identical title text preserves native replacement identity behavior', 'document.title="same";var t=document.getElementsByTagName("title")[0],old=t.firstChild;document.title="same";(old===t.firstChild)+":"+(old.parentNode===t);', { initialHtml });
add('document title null converts to a string', 'document.title=null;document.title;', { initialHtml });
add('document title setter with no argument converts undefined', 'Object.getOwnPropertyDescriptor(Document.prototype,"title").set.call(document);document.title;', { initialHtml });
add('title text setter with no argument converts undefined', 'var t=document.createElement("title");Object.getOwnPropertyDescriptor(HTMLTitleElement.prototype,"text").set.call(t);t.text;');
add('innerHTML setter with no argument converts undefined', 'var e=document.createElement("div");Object.getOwnPropertyDescriptor(Element.prototype,"innerHTML").set.call(e);e.innerHTML;');
add('className setter with no argument requires a value', 'try{Object.getOwnPropertyDescriptor(Element.prototype,"className").set.call(document.createElement("div"));}catch(e){e.name;}');
add('textContent setter with no argument requires a value', 'try{Object.getOwnPropertyDescriptor(Node.prototype,"textContent").set.call(document.createElement("div"));}catch(e){e.name;}');
add('document head and body getters ignore nested names', 'var nested=document.createElement("head");document.body.appendChild(nested);(document.head.parentNode===document.documentElement)+":"+(document.body.parentNode===document.documentElement);', { initialHtml });
add('canvas dimensions have native missing-attribute defaults', 'var c=document.createElement("canvas");c.width+":"+c.height+":"+c.getAttribute("width")+":"+c.getAttribute("height");');
for (const name of ['width','height']) {
  for (const value of ['', '0', '+1', '-0', '-1', ' 8', '\t8x', '1e2', '1.5', '0x20', '2147483647', '2147483648', '4294967295', '4294967296', '9999999999999999999999', 'Infinity', '08', '\u00a08', '8 9', '-000x', '+ 8', '\u000b8']) {
    add(`canvas ${name} attribute parses ${JSON.stringify(value)}`, `var c=document.createElement("canvas");c.setAttribute(${JSON.stringify(name)},${JSON.stringify(value)});c.${name}+":"+c.getAttribute(${JSON.stringify(name)});`);
  }
  for (const value of ['undefined','null','false','true','0','-0','-1','1.8','NaN','Infinity','-Infinity','2147483647','2147483648','4294967295','4294967296','-4294967295','"1e2"']) {
    add(`canvas ${name} setter converts ${value}`, `var c=document.createElement("canvas");c.${name}=${value};c.${name}+":"+c.getAttribute(${JSON.stringify(name)});`);
  }
  add(`canvas ${name} removes its reflected dimension`, `var c=document.createElement("canvas");c.${name}=8;c.removeAttribute(${JSON.stringify(name)});c.${name}+":"+c.getAttribute(${JSON.stringify(name)});`);
}
add('canvas dimension setter uses number-hint source conversion', 'var c=document.createElement("canvas"),s="";c.width={valueOf:function(){s+="v";return {};},toString:function(){s+="s";return "8";}};s+":"+c.width;');
add('canvas dimension conversion throw preserves prior size', 'var c=document.createElement("canvas");c.width=8;try{c.width={valueOf:function(){throw 7;}};}catch(e){e+":"+c.width;}');
add('canvas setter rejects wrong receiver before source conversion', 'var s="";try{Object.getOwnPropertyDescriptor(HTMLCanvasElement.prototype,"width").set.call(document.createElement("div"),{valueOf:function(){s+="v";return 8;}});}catch(e){s+=e.name;}s;');
add('canvas setter with no argument converts undefined to zero', 'var c=document.createElement("canvas");Object.getOwnPropertyDescriptor(HTMLCanvasElement.prototype,"width").set.call(c);c.width;');
add('canvas 2D context preserves identity prototype and canvas back-reference', 'var c=document.createElement("canvas"),x=c.getContext("2d");(x===c.getContext("2d"))+":"+(x.canvas===c)+":"+(x instanceof CanvasRenderingContext2D)+":"+c.width+":"+c.height;');
add('canvas 2D attributes reflect initial alpha and macOS desynchronized setting', 'var c=document.createElement("canvas"),x=c.getContext("2d",{alpha:false,desynchronized:true}),a=x.getContextAttributes();a.alpha+":"+a.desynchronized+":"+Object.keys(a).join(",")+":"+(a!==x.getContextAttributes());');
add('cached canvas context ignores later creation settings after conversion', 'var c=document.createElement("canvas"),x=c.getContext("2d",{alpha:false}),s="";var y=c.getContext("2d",{get alpha(){s+="a";return true;}});(x===y)+":"+s+":"+y.getContextAttributes().alpha;');
const canvasOptionNames=['alpha','antialias','depth','failIfMajorPerformanceCaveat','powerPreference','premultipliedAlpha','preserveDrawingBuffer','stencil','desynchronized','xrCompatible'];
for(const type of ['2d','unknown','2D']) add(`canvas option getters run in pinned order for ${type}`, `var c=document.createElement("canvas"),s="",o={},names=${JSON.stringify(canvasOptionNames)};for(var i=0;i<names.length;i++)(function(n){Object.defineProperty(o,n,{get:function(){s+=n+":";return n==="powerPreference"?"default":true;}});})(names[i]);var x=c.getContext(${JSON.stringify(type)},o);s+!!x;`);
for(const expression of ['undefined','null','false','0','"x"']) add(`canvas options permissive dictionary conversion ${expression}`, `var x=document.createElement("canvas").getContext("2d",${expression});x.getContextAttributes().alpha;`);
for(const expression of ['"default"','"low-power"','"high-performance"','null','"invalid"']) add(`canvas powerPreference enum ${expression}`, `var c=document.createElement("canvas");try{!!c.getContext("2d",{powerPreference:${expression}});}catch(e){e.name;}`);
add('canvas ID and enum source conversions preserve dictionary order', 'var c=document.createElement("canvas"),s="";c.getContext({toString:function(){s+="t";return "2d";}},{get alpha(){s+="a";return false;},get powerPreference(){s+="p";return {toString:function(){s+="s";return "low-power";}};},get stencil(){s+="n";return true;}});s;');
add('canvas invalid enum stops later option getter', 'var c=document.createElement("canvas"),s="";try{c.getContext("2d",{get powerPreference(){s+="p";return "invalid";},get stencil(){s+="wrong";}});}catch(e){s+=e.name;}s;');
add('canvas option throw preserves existing context identity', 'var c=document.createElement("canvas"),x=c.getContext("2d"),s="";try{c.getContext("2d",{get alpha(){throw 7;}});}catch(e){s+=e;}s+":"+(c.getContext("2d")===x);');
add('reentrant option getter can create the context before outer settings', 'var c=document.createElement("canvas"),inner;var outer=c.getContext("2d",{get alpha(){inner=c.getContext("2d");return false;}});(inner===outer)+":"+outer.getContextAttributes().alpha;');
add('existing 2D context rejects incompatible recognized context modes', 'var c=document.createElement("canvas");c.getContext("2d");c.getContext("webgl")+":"+c.getContext("bitmaprenderer");');
add('canvas unknown context type returns null without creating a context', 'var c=document.createElement("canvas"),a=c.getContext("unknown");c.width=8;a+":"+c.width+":"+c.getContext("2d").getContextAttributes().alpha;');
add('canvas getContext required argument and receiver checks precede conversion', 'var s="",c=document.createElement("canvas");try{c.getContext();}catch(e){s+=e.name;}try{HTMLCanvasElement.prototype.getContext.call(document.createElement("div"),{toString:function(){s+="wrong";return "2d";}});}catch(e){s+=":"+e.name;}s;');
add('canvas context methods reject wrong receivers', 'var s="";try{CanvasRenderingContext2D.prototype.getContextAttributes.call({});}catch(e){s+=e.name;}try{Object.getOwnPropertyDescriptor(CanvasRenderingContext2D.prototype,"canvas").get.call({});}catch(e){s+=":"+e.name;}s;');
add('canvas pixel readback remains explicit after deferred painting', 'var ctx=document.createElement("canvas").getContext("2d");ctx.fillRect(0,0,1,1);ctx.getImageData(0,0,1,1);', { expectedStatus:'unresolved' });
add('canvas context dimension reset retains context identity', 'var c=document.createElement("canvas"),x=c.getContext("2d");c.width=8;(x===c.getContext("2d"))+":"+c.width;');
add('native non-2D context creation remains explicit', 'document.createElement("canvas").getContext("webgl");', { expectedStatus:'unresolved' });
add('initial pinned-shape document creates native doctype and inert script text', 'var d=document.firstChild;d.nodeType+":"+d.name+":"+(d instanceof DocumentType)+":"+document.getElementById("a").textContent+":"+document.getElementsByTagName("script").length;', { initialHtml });
add('separate scripts preserve state and hoist separately', 'var a=1;', { followups: ['var b=a+2;', 'a+b;'], completedPrograms: 3 });
add('later script declarations replace earlier global bindings', 'var f=9;f;', { followups: ['function f(){return 7;}f();'], completedPrograms: 2 });
add('unresolved script stops before followup entropy is consumed', 'document.createElement("div").getBoundingClientRect();', { followups: ['Math.random();'], randomInputs: [123], expectedStatus: 'unresolved', randomInputsRemaining: 1, executedPrograms: 1, completedPrograms: 0 });
add('unsupported initial document stops before any source executes', 'Math.random();', { initialHtml: '<html><body>missing explicit head and doctype</body></html>', randomInputs: [123], expectedStatus: 'unresolved', randomInputsRemaining: 1, executedPrograms: 0, completedPrograms: 0 });
add('style getter preserves SameObject and native prototype', 'var e=document.createElement("div");(e.style===e.style)+":"+(e.style instanceof CSSStyleDeclaration);');
const nativeCssProperties=JSON.parse(readFileSync(new URL('../model/css-properties.json',import.meta.url),'utf8')).properties;
const mappedCssProperties=nativeCssProperties.filter(property=>property.cssName!==null);
add('all captured mapped CSS named properties read empty and remain present', `var s=document.createElement("div").style,names=${JSON.stringify(mappedCssProperties.map(property=>property.javascriptName))},out=[];for(var i=0;i<names.length;i++){var n=names[i];out.push(n+":"+s[n]+":"+(n in s));}out.join("|");`);
add('all captured empty CSS aliases can be queried and removed without attribute mutation', `var e=document.createElement("div"),s=e.style,names=${JSON.stringify([...new Set(mappedCssProperties.flatMap(property=>property.aliases))])},out=[];for(var i=0;i<names.length;i++){var n=names[i];out.push(s.getPropertyValue(n)+s.getPropertyPriority(n)+s.removeProperty(n));}out.length+":"+out.join("")+":"+e.getAttribute("style");`);
add('CSS scale assignment preserves its expression result', 'document.createElement("div").style.transform="scale(0.5)";');
add('unsupported 3D CSS transform remains explicit', 'document.createElement("div").style.transform="translate3d(0px,1px,0px)";', {expectedStatus:'unresolved'});
add('CSS native aliases read existing supported canonical values', 'var s=document.createElement("div").style;s.opacity="0.5";s.background="url(img/x.png)";s.webkitOpacity+":"+s.backgroundOrigin+":"+s.getPropertyValue("-webkit-background-origin");');
add('unknown CSS named property is absent after complete interface lookup', 'var s=document.createElement("div").style;typeof s.cookieClickerAuditAbsent+":"+("cookieClickerAuditAbsent" in s)+":"+s["01"];');
add('CSS legacy named properties remain explicit', 'document.createElement("div").style.epubCaptionSide;', {expectedStatus:'unresolved'});
add('CSS unknown shorthand with present longhands remains explicit', 'var s=document.createElement("div").style;s.overflowX="hidden";s.getPropertyValue("overflow");', {expectedStatus:'unresolved'});
add('native game blend-mode feature detection reads a supported empty property', 'document.createElement("detect").style.mixBlendMode==="";');
for(const value of ['auto','pointer',' POINTER ','inherit',''])add(`CSS source cursor ${JSON.stringify(value)}`,
  `var s=document.createElement("div").style;s.cursor="auto";s.cursor=${JSON.stringify(value)};s.cursor+":"+s.cssText;`);
add('CSS source cursor conversion preserves callback order','var log="",s=document.createElement("div").style;s.cursor={toString:function(){log+="s";return "pointer";}};log+":"+s.cursor;');
add('CSS cursor image and other keyword grammar remains explicit','document.createElement("div").style.cursor="crosshair";',{expectedStatus:'unresolved'});
add('native heralds style keeps bold weight when display changes', 'var e=document.createElement("div");e.setAttribute("style","position:relative;display:none;font-weight:bold;");e.style.display="inline-block";e.style.cssText;');
for(const value of ['normal','BOLD','bolder','lighter','1','100','400','900','1000','0','1001','-1','+400','000400','invalid','']){
  add(`CSS fontWeight ${value}`, `var s=document.createElement("div").style;s.fontWeight="bold";s.fontWeight=${JSON.stringify(value)};s.fontWeight+":"+s.cssText;`);
}
add('fractional font-weight remains explicit', 'document.createElement("div").style.fontWeight="450.5";', {expectedStatus:'unresolved'});
for (const value of ['normal','MULTIPLY','screen','overlay','darken','lighten','color-dodge','color-burn','hard-light','soft-light','difference','exclusion','hue','saturation','color','luminosity','initial','inherit','unset','revert','plus-lighter','invalid','']) {
  add(`CSS mixBlendMode keyword ${JSON.stringify(value)}`, `var s=document.createElement("div").style;s.mixBlendMode="multiply";s.mixBlendMode=${JSON.stringify(value)};s.mixBlendMode+":"+s.cssText;`);
}
add('native tiny globe declaration normalizes after position assignment', 'var e=document.createElement("div");e.setAttribute("style","position:absolute;top:-4px;width:22px;height:22px;background:url(img/tinyglobeSheet.gif);right:4px;top:4px;pointer-events:none;");e.style.backgroundPosition="-418px";e.style.cssText+":"+e.style.backgroundPosition+":"+e.style.background;');
add('CSS setter invokes source conversion and preserves assignment result', 'var e=document.createElement("div"),log="",v={toString:function(){log+="s";return "3px";}};var result=(e.style.left=v);log+":"+(result===v)+":"+e.style.left;');
add('invalid CSS setter preserves raw style attribute', 'var e=document.createElement("div");e.setAttribute("style","left:2px");e.style.left="bad";e.getAttribute("style");');
add('null CSS setter removes property', 'var e=document.createElement("div");e.style.left="2px";e.style.left=null;e.style.left+":"+e.getAttribute("style");');
for (const expression of ['undefined','{toString:function(){return null;}}','{toString:function(){return undefined;}}']) {
  add(`CSS setter preserves existing property after invalid converted ${expression}`, `var e=document.createElement("div");e.style.left="2px";e.style.left=${expression};e.style.left+":"+e.getAttribute("style");`);
}
add('CSS object priority returning null remains an invalid string priority', 'var s=document.createElement("div").style;s.left="2px";s.setProperty("left","3px",{toString:function(){return null;}});s.left;');
for (const value of ['\v1px','1px\v','\vauto','\v0','\v1%','\v-1px','\v\t1px',' \v1px','\v1px ','\v1px\t','\v\v1px','\v+1px','\v1 px']) {
  for (const mode of ['property','cssText','attribute']) {
    const assignment=mode==='property'?`e.style.left=${JSON.stringify(value)};`:mode==='cssText'?`e.style.cssText=${JSON.stringify('left:'+value)};`:`e.setAttribute("style",${JSON.stringify('left:'+value)});`;
    add(`CSS ${mode} vertical-tab boundary ${JSON.stringify(value)}`, `var e=document.createElement("div");e.style.left="2px";${assignment}e.style.left;`);
  }
}
for (const name of ['top','right','bottom','width','height','minWidth','minHeight','maxWidth','maxHeight']) {
  add(`CSS native length fast-path membership ${name}`, `var s=document.createElement("div").style;s.${name}="2px";s.${name}="\\u000b1px";s.${name};`);
}
for (const value of ['+1px','+0','+01px','+-1px','++1px']) {
  add(`CSS signed integer token ${value}`, `var s=document.createElement("div").style;s.left="2px";s.left=${JSON.stringify(value)};s.left;`);
}
add('CSS duplicate declarations follow important precedence and final order', 'var e=document.createElement("div");e.style.cssText="left:1px!important;top:2px;left:3px;top:4px;";e.style.cssText+":"+e.style.getPropertyPriority("left");');
add('CSS property assignment replaces priority', 'var e=document.createElement("div");e.style.setProperty("left","2px","important");e.style.left="3px";e.style.cssText+":"+e.style.getPropertyPriority("left");');
add('CSSOM mutation preserves order independently of parser important grouping', 'var e=document.createElement("div");e.style.cssText="left:1px;top:2px;";e.style.setProperty("left","3px","important");e.style.cssText+":"+e.style.item(0);');
add('setting the same style attribute reparses CSSOM order', 'var e=document.createElement("div");e.style.cssText="left:1px;top:2px;";e.style.setProperty("left","3px","important");var before=e.style.cssText;e.setAttribute("style",e.getAttribute("style"));before+":"+e.style.cssText;');
add('CSS property and priority conversions precede mutation', 'var e=document.createElement("div"),log="";e.style.setProperty({toString:function(){log+="n";return "left";}},{toString:function(){log+="v";return "4px";}},{toString:function(){log+="p";return "IMPORTANT";}});log+":"+e.style.cssText;');
add('CSS invalid priority ignores nonempty and empty values in Chromium87', 'var e=document.createElement("div");e.style.left="2px";e.style.setProperty("left","4px","bad");var before=e.style.left;e.style.setProperty("left","","bad");before+":"+e.style.left;');
add('CSS empty cssText creates empty style attribute', 'var e=document.createElement("div");e.style.cssText="";e.getAttribute("style");');
add('cssText setter with no argument parses undefined as empty declaration', 'var s=document.createElement("div").style;s.left="2px";Object.getOwnPropertyDescriptor(CSSStyleDeclaration.prototype,"cssText").set.call(s);s.cssText;');
add('CSS removeProperty returns previous value and retains other properties', 'var e=document.createElement("div");e.style.cssText="left:1px;top:2px;";e.style.removeProperty("left")+":"+e.style.cssText;');
for(const value of ['transparent','TRANSPARENT','  transparent\t']) {
 add('CSS transparent background source shorthand '+JSON.stringify(value),`var e=document.createElement('div'),s=e.style;s.background=${JSON.stringify(value)};var out=[];for(var i=0;i<s.length;i++)out.push(s.item(i)+'='+s.getPropertyValue(s[i]));s.background+':'+s.cssText+':'+out.join(';');`);
}
for(const initial of ['url(img/x.png)','url(img/x.png) 7px 9px','inherit']) {
 add('CSS transparent shorthand resets image and position '+initial,`var s=document.createElement('div').style;s.background=${JSON.stringify(initial)};s.background='transparent';s.background+':'+s.backgroundImage+':'+s.backgroundPosition+':'+s.backgroundColor+':'+s.cssText;`);
}
for(const pos of ['','7px','left top'])add('CSS transparent background position serialization '+pos,
 `var s=document.createElement('div').style;s.background='transparent';${pos?`s.backgroundPosition=${JSON.stringify(pos)};`:''}s.background+':'+s.cssText;`);
add('CSS mixed global background shorthand serialization remains explicit',`var s=document.createElement('div').style;s.background='transparent';s.backgroundPosition='inherit';s.cssText;`,{expectedStatus:'unresolved'});
for(const priority of ['', 'important']) for(const property of ['background','background-position']) add('CSS native shorthand removal returns empty '+property+priority,`var s=document.createElement('div').style;s.setProperty(${JSON.stringify(property)},${JSON.stringify(property==='background'?'transparent':'7px')},${JSON.stringify(priority)});s.removeProperty(${JSON.stringify(property)})+':'+s.cssText;`);
add('CSS transparent color as a standalone declaration',`var s=document.createElement('div').style;s.backgroundColor='transparent';s.background+':'+s.backgroundColor+':'+s.cssText;`);
add('CSS transparent color longhand joins existing image',`var s=document.createElement('div').style;s.background='url(img/x.png) 7px 9px';s.backgroundColor='transparent';s.background+':'+s.cssText;`);
add('CSS transparent background keeps priority and native order',`var s=document.createElement('div').style;s.height='7px';s.setProperty('background','transparent','important');s.width='8px';s.cssText+':'+s.getPropertyPriority('background')+':'+s.removeProperty('background')+':'+s.cssText;`);
add('CSS transparent attribute preserves raw text until mutation',`var e=document.createElement('div');e.setAttribute('style','BACKGROUND: TRANSPARENT!important; height: 7px');var before=e.getAttribute('style')+':'+e.style.background;e.style.width='8px';before+':'+e.getAttribute('style');`);
add('CSS transparent background source ToString runs once',`var s=document.createElement('div').style,log='';s.background={toString:function(){log+='convert';s.width='9px';return 'transparent';}};log+':'+s.cssText;`);
add('CSS transparent background throwing conversion preserves value',`var s=document.createElement('div').style;s.background='transparent';try{s.background={toString:function(){throw 'stop';}};}catch(e){}s.cssText;`);
add('CSS transparent background direct null removes declaration',`var s=document.createElement('div').style;s.background='transparent';s.background=null;s.cssText+':'+s.length;`);
for(const property of ['color','backgroundColor','background'])for(const value of ['#000','#fff','#ce2549','#79c600','#a6abad','#1234','#112233fe','rgba(255,255,255,0.7)','rgb(-1,999,0)','rgb(50%,25%,0%)','transparent','RED','currentColor']) {
 add('CSS parsed color '+property+' '+value,`var e=document.createElement('div'),s=e.style;s.${property}=${JSON.stringify(value)};s.${property}+':'+s.cssText+':'+e.getAttribute('style');`);
}
for(const property of ['color','background-color'])for(const priority of ['', 'important'])add('CSS color priority and removal '+property+priority,
 `var s=document.createElement('div').style;s.setProperty(${JSON.stringify(property)},'#1234',${JSON.stringify(priority)});s.cssText+':'+s.getPropertyPriority(${JSON.stringify(property)})+':'+s.removeProperty(${JSON.stringify(property)})+':'+s.cssText;`);
add('CSS color source conversion preserves side effects',`var s=document.createElement('div').style,log='';s.color={toString:function(){log+='c';s.backgroundColor='#000';return '#fff';}};log+':'+s.cssText;`);
add('CSS color invalid hex leaves prior declaration',`var s=document.createElement('div').style;s.color='#fff';s.color='#ggg';s.color+':'+s.cssText;`);
add('CSS color throwing source conversion preserves prior declaration',`var s=document.createElement('div').style;s.color='#fff';try{s.color={toString:function(){throw 'stop';}};}catch(e){}s.cssText;`);
for(const value of ['hsl(0,100%,50%)','rebeccapurple','rgb(1 2 3)','rgb(1,2,3,50%)'])add('CSS color additional grammar remains explicit '+value,`document.createElement('div').style.color=${JSON.stringify(value)};`,{expectedStatus:'unresolved'});
const marketColorSource=loadGameSource().sources['minigameMarket.js'];
const marketColorStart=marketColorSource.indexOf('M.colBases=['),marketColorEnd=marketColorSource.indexOf('M.setCols();',marketColorStart)+'M.setCols();'.length;
assert(marketColorStart>=0&&marketColorEnd>marketColorStart);
const marketColorStatements=marketColorSource.slice(marketColorStart,marketColorEnd);
for(const selection of [-1,0,1,2])for(const graph of [false,true])add('actual market color palette and setCols source '+selection+':'+graph,
 `var box=document.createElement('div');function l(id){return id==='bankGraphBox'?box:null;}var M={graphCols:${selection},graph:${graph?"document.createElement('canvas')":'null'}};${marketColorStatements}M.graphCols+':'+box.style.cssText+':'+(M.graph?M.graph.style.cssText:'no graph');`);
const backgroundTransparentStatement=loadGameSource().sources['main.js'].split('\n').find(line=>line.includes("l('backgroundCanvas').style.background='transparent';"));
assert.equal(backgroundTransparentStatement.trim(),"l('backgroundCanvas').style.background='transparent';");
add('actual DrawBackground transparent assignment statement',`var canvas=document.createElement('canvas');function l(id){if(id!=='backgroundCanvas')throw 'wrong target';return canvas;}${backgroundTransparentStatement}canvas.style.background+':'+canvas.getAttribute('style');`);
add('CSS background shorthand exposes native longhand order', 'var e=document.createElement("div");e.style.background="url(img/x.png)";var s=e.style,out=[];for(var i=0;i<s.length;i++)out.push(s.item(i)+"="+s.getPropertyValue(s[i]));out.join(";");');
add('CSS method property names follow native case handling', 'var e=document.createElement("div");e.style.setProperty("LEFT","3px");e.style.getPropertyValue("LEFT")+":"+e.style.getPropertyValue("left");');
add('CSS unsupported numeric precision stays explicit', 'document.createElement("div").style.left="1.123456789px";', { expectedStatus: 'unresolved' });
add('CSS reflection on exotic own properties stays explicit', 'Object.getOwnPropertyDescriptor(document.createElement("div").style,"left");', { expectedStatus: 'unresolved' });
for (const value of ['', '-418px', '3px', 'left', 'center', 'right', 'top', 'bottom', '3px 2px', '0', '0 0', '50%', '-22px', 'left top', 'top left', 'center left', 'right 2px', 'top 3px', '3px top', '3px left', 'bottom center', 'center 3px', '3px\t2px']) {
  add(`CSS background position ${JSON.stringify(value)}`, `var s=document.createElement("div").style;s.backgroundPosition=${JSON.stringify(value)};s.backgroundPosition+":"+s.cssText+":"+s.length;`);
}
add('classList preserves SameObject and native prototype', 'var e=document.createElement("div");(e.classList===e.classList)+":"+(e.classList instanceof DOMTokenList);');
add('classList reads unique ordered tokens without rewriting raw value', 'var e=document.createElement("div");e.className=" a  a b ";e.classList.length+":"+e.classList[0]+":"+e.classList.item(1)+":"+e.classList.value+":"+e.classList.toString();');
add('classList contains does not validate empty or whitespace query tokens', 'var s=document.createElement("div").classList;s.contains("")+":"+s.contains("a b");');
add('classList add keeps first occurrence and serializes the set', 'var e=document.createElement("div");e.className=" a a b ";e.classList.add("b","c","a");e.className;');
add('classList remove normalizes an existing attribute even if token is absent', 'var e=document.createElement("div");e.className=" a a b ";e.classList.remove("z");e.className;');
add('classList add with zero arguments creates an empty attribute', 'var e=document.createElement("div");e.classList.add();e.getAttribute("class");');
add('classList remove preserves an absent attribute', 'var e=document.createElement("div");e.classList.remove("a");e.getAttribute("class");');
add('classList token conversion finishes before validation and preserves old value on throw', 'var e=document.createElement("div"),log="";e.className="old";try{e.classList.add({toString:function(){log+="a";return "";}},{toString:function(){log+="b";return "x";}});}catch(error){log+=error.name;}log+":"+e.className;');
add('classList rejects HTML whitespace tokens', 'var s=document.createElement("div").classList;try{s.add("a b");}catch(error){error.name;}');
add('classList keeps non-ASCII whitespace inside a token', 'var e=document.createElement("div");e.className="a b c";e.classList.length+":"+e.classList.item(0);');
add('classList no-op forced toggle preserves the raw attribute', 'var e=document.createElement("div");e.className=" a  a b ";var r=e.classList.toggle("a",true);r+":"+e.className;');
add('classList explicit undefined force means omitted force', 'var e=document.createElement("div");e.classList.toggle("x",undefined)+":"+e.className;');
add('classList toggle force uses truthiness without source conversion', 'var e=document.createElement("div"),log="";var r=e.classList.toggle("x",{valueOf:function(){log+="v";return 0;}});r+":"+log+":"+e.className;');
add('classList absent replacement preserves raw attribute', 'var e=document.createElement("div");e.className=" a a b ";e.classList.replace("z","x")+":"+e.className;');
for (const [before, old, newer] of [['a b c','a','c'],['a b c','c','a'],['a b c','b','a'],['a b c','b','c']]) {
  add(`classList replacement ${old} to ${newer}`, `var e=document.createElement("div");e.className=${JSON.stringify(before)};e.classList.replace(${JSON.stringify(old)},${JSON.stringify(newer)})+":"+e.className;`);
}
add('classList value setter preserves raw spacing and converts null as DOMString', 'var e=document.createElement("div");e.classList.value=" a  a ";var first=e.classList.value;e.classList.value=null;first+":"+e.className;');
add('classList value setter with no argument converts undefined', 'var s=document.createElement("div").classList;Object.getOwnPropertyDescriptor(DOMTokenList.prototype,"value").set.call(s);s.value;');
add('classList item distinguishes null result from indexed undefined', 'var e=document.createElement("div");e.className="x";e.classList.item(undefined)+":"+e.classList.item(-1)+":"+(e.classList[8]===undefined);');
add('classList forEach is the same generic native Array function', '(DOMTokenList.prototype.forEach===Array.prototype.forEach)+":"+(function(){var out=[];DOMTokenList.prototype.forEach.call({0:"x",length:1},function(v){out.push(v);});return out.join(":");})();');
add('classList forEach captures length and reads live values', 'var e=document.createElement("div"),out=[];e.className="a b";e.classList.forEach(function(token,index,list){out.push(token+index);if(index===0)list.add("c");});out.join(":")+":"+e.className;');
add('classList forEach sees shifts caused by removal', 'var e=document.createElement("div"),out=[];e.className="a b c";e.classList.forEach(function(token,index,list){out.push(token);if(index===0)list.remove("b");});out.join(":");');
add('Array slice reads host token indices through saved continuations', 'var e=document.createElement("div");e.className="a b c";Array.prototype.slice.call(e.classList,1).join(":");');
add('Array indexOf queries live host token presence', 'var e=document.createElement("div");e.className="a b c";Array.prototype.indexOf.call(e.classList,"b")+":"+Array.prototype.indexOf.call(e.classList,"a",1);');
add('Array lastIndexOf queries host token presence in reverse', 'var e=document.createElement("div");e.className="a b c";Array.prototype.lastIndexOf.call(e.classList,"b",-1)+":"+Array.prototype.lastIndexOf.call(e.classList,"c",-2);');
add('Array reduce resumes source callbacks on host tokens', 'var e=document.createElement("div");e.className="a b c";Array.prototype.reduce.call(e.classList,function(a,b){return a+":"+b;});');
add('Array reduceRight resumes source callbacks on host tokens', 'var e=document.createElement("div");e.className="a b c";Array.prototype.reduceRight.call(e.classList,function(a,b){return a+":"+b;},"x");');
add('host token indexed in operator distinguishes absent properties', 'var e=document.createElement("div");e.className="a b";(0 in e.classList)+":"+(2 in e.classList);');
add('generic Array mutation on readonly host indices stays explicit', 'var e=document.createElement("div");e.className="a b";Array.prototype.push.call(e.classList,"c");', { expectedStatus: 'unresolved' });
add('Array sort preserves host comparator continuation before readonly writes', 'var e=document.createElement("div"),log="";e.className="c a b";try{Array.prototype.sort.call(e.classList,function(a,b){log+=a+":"+b;throw "stop";});}catch(error){log+=":"+error;}log+":"+e.className;');
add('Array sort reads HTMLCollection indices before comparator throw', 'var e=document.createElement("div"),log="";e.innerHTML="<b id=c></b><b id=a></b><b id=b></b>";try{Array.prototype.sort.call(e.getElementsByTagName("b"),function(a,b){log+=a.id+":"+b.id;throw "stop";});}catch(error){log+=":"+error;}log+":"+e.firstChild.id;');
add('Object defineProperty resumes descriptor HasProperty on native classList', 'var e=document.createElement("div"),o={};e.className=" value ";Object.defineProperty(o,"x",e.classList);var d=Object.getOwnPropertyDescriptor(o,"x");o.x+":"+d.writable+":"+d.enumerable+":"+d.configurable;');
add('classList supports has no supported-token vocabulary', 'try{document.createElement("div").classList.supports("x");}catch(error){error.name;}');
add('classList missing arguments and wrong receivers fail before conversion', 'var log="",s=document.createElement("div").classList;try{s.contains();}catch(error){log+=error.name;}try{DOMTokenList.prototype.add.call({}, {toString:function(){log+="bad";return "x";}});}catch(error){log+=":"+error.name;}log;');

const requests = cases.map(c => ({ ast: compileJavaScript(c.source, { name: c.name }), fuel: 500000,
  browserLibrary: true, randomInputs: c.randomInputs || [],
  ...(c.initialHtml === undefined ? {} : { initialHtmlUnits: units(c.initialHtml) }),
  ...(c.followups === undefined ? {} : { followupPrograms: c.followups.map((source, index) => compileJavaScript(source, { name: `${c.name}:${index + 1}` })) }) }));
const child = spawnSync(fileURLToPath(new URL('.lake/build/bin/jsastcheck', import.meta.url)), ['--execute'], {
  input: JSON.stringify(requests), encoding: 'utf8', timeout: 60000, maxBuffer: 8 * 1024 * 1024,
});
if (child.error) throw child.error;
assert.equal(child.status, 0, child.stderr);
const observed = JSON.parse(child.stdout);
const worker = function (cases) {
  const encode = value => {
    if (value === undefined) return { type: 'undefined' };
    if (value === null) return { type: 'null' };
    if (typeof value === 'boolean') return { type: 'boolean', value };
    if (typeof value === 'string') return { type: 'string', units: Array.from({ length: value.length }, (_, i) => value.charCodeAt(i)) };
    if (typeof value === 'number') { const view = new DataView(new ArrayBuffer(8)); view.setFloat64(0, value, false); return { type: 'number', bits: view.getBigUint64(0, false).toString() }; }
    throw new Error('Browser comparison source must return a primitive');
  };
  return cases.map(c => {
    if (c.expectedStatus) return { status: c.expectedStatus };
    const savedRandom = Math.random;
    // Prepared diagnostic entropy only; never an admissible strategy action.
    if (c.randomInputs) { let index = 0; Math.random = () => c.randomInputs[index++] / 9007199254740992; }
    try {
      const run = function (sources, document) { let auditLastCompletion; for (const source of sources) auditLastCompletion = eval(source); return auditLastCompletion; };
      const fixtureDocument = c.initialHtml === undefined ? document : new DOMParser().parseFromString(c.initialHtml.replace(/^\ufeff/, ''), 'text/html');
      return { status: 'complete', value: encode(run([c.source, ...(c.followups || [])], fixtureDocument)) };
    }
    catch (cause) { return { status: 'throw', name: cause.name, message: cause.message }; }
    finally { Math.random = savedRandom; }
  });
};
const native = runNativeBrowser(worker.toString(), cases, { allowEval: true, allowInlineStyles: true });
const failures = [];
for (let i = 0; i < cases.length; i += 1) {
  try {
    if (cases[i].expectedStatus) assert.equal(observed[i].status, cases[i].expectedStatus);
    else assert.deepEqual({ status: observed[i].status, value: observed[i].value }, native.result[i]);
    if (cases[i].timerCount !== undefined) assert.equal(observed[i].timerCount, cases[i].timerCount);
    if (cases[i].randomInputsRemaining !== undefined) assert.equal(observed[i].randomInputsRemaining, cases[i].randomInputsRemaining);
    if (cases[i].executedPrograms !== undefined) assert.equal(observed[i].executedPrograms, cases[i].executedPrograms);
    if (cases[i].completedPrograms !== undefined) assert.equal(observed[i].completedPrograms, cases[i].completedPrograms);
  } catch (error) { failures.push({ name: cases[i].name, observed: observed[i], expected: native.result[i], error: error.message }); }
}
if (failures.length) { console.error(JSON.stringify(failures, null, 2)); process.exitCode = 1; }
console.log(JSON.stringify({ cases: cases.length, passed: cases.length - failures.length, versions: native.versions,
  executableHash: native.executableHash, gameEntryPointExecuted: false, javascriptSemanticsVerified: false }));

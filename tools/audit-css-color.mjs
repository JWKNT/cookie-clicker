/** Pinned native color code and actual game assignment inventory; no coverage proof. */
import assert from 'node:assert/strict';
import{readFileSync,writeFileSync}from'node:fs';
import{createHash}from'node:crypto';
import{createRequire}from'node:module';
import{loadGameSource}from'../model/game-source.mjs';
const{parse}=createRequire(new URL('../source/cookie-monster-plus/package.json',import.meta.url))('acorn');
const paths={'color.cc':'platform/graphics/color.cc','color.h':'platform/graphics/color.h',
 'css_color_value.cc':'core/css/css_color_value.cc','css_parser_fast_paths.cc':'core/css/parser/css_parser_fast_paths.cc',
 'canvas_style.cc':'modules/canvas/canvas2d/canvas_style.cc','canvas_style.h':'modules/canvas/canvas2d/canvas_style.h','decimal.cc':'platform/wtf/decimal.cc'};
const sources=Object.entries(paths).map(([file,path])=>{const text=readFileSync(new URL(`../model/browser-source/chromium-87/${file}`,import.meta.url),'utf8');return{file,url:`https://github.com/chromium/chromium/blob/87.0.4280.141/third_party/blink/renderer/${path}`,sha256:createHash('sha256').update(text).digest('hex')};});
assert.match(readFileSync(new URL('../model/browser-source/chromium-87/css_color_value.cc',import.meta.url),'utf8'),/round\(alphavalue \* 100 \/ 255\.0f\)/);
assert.match(readFileSync(new URL('../model/browser-source/chromium-87/decimal.cc',import.meta.url),'utf8'),/const int kMaxDigits = DBL_DIG/);
const game=loadGameSource(),assignments=[];
for(const[name,source]of Object.entries(game.sources)){
 if(!name.endsWith('.js'))continue;
 const ast=parse(source,{ecmaVersion:2020,locations:true});
 const walk=node=>{if(!node||typeof node!=='object')return;
  if(node.type==='AssignmentExpression'&&node.left.type==='MemberExpression'){
   const property=node.left.computed?node.left.property.value:node.left.property.name;
   if(['fillStyle','strokeStyle','shadowColor','backgroundColor','color'].includes(property))assignments.push({name,line:node.loc.start.line,property,value:source.slice(node.right.start,node.right.end)});
  }
  for(const[key,value]of Object.entries(node))if(key!=='loc'){
   if(Array.isArray(value))value.forEach(walk);else if(value&&typeof value==='object')walk(value);
  }
 };walk(ast);
}
const report={schema:1,scope:'closed native eight-bit RGBA parsing and distinct CSSOM/Canvas text',chromiumVersion:'87.0.4280.141',sources,
 gameSourceHashes:game.hashes,assignmentInventory:assignments,
 implementation:{storage:'RGBA uses four UInt8 values; no pixel readback or renderer snapshot is supplied.',grammar:'Hex3/4/6/8, twenty explicit base color keywords, comma rgb/rgba with consistent numeric or percent channels and bounded six-digit decimal parts. Other grammar or environment-dependent colors remain explicit.',numeric:'Native binary64 parse/divide/multiply/round order, negative clamps and byte clamps are represented by the logical Float.Model.',cssText:'Accepted keyword identity is retained; numeric values use CSSColorValue rgb/rgba text. The actual byte-alpha two/three-decimal choice is proved equal to the logical Float32 source calculation for all256 bytes in JavaScriptCssColorAlpha.lean.',canvasText:'Opaque colors use lowercase six-digit hex. Alpha uses binary64 byte/255, ECMAScript shortest text and the native Decimal15-digit reduction.'},
 validation:'node lean/check_javascript_color.mjs --engine',
 remaining:['General CSS color parser and named/system colors','CurrentColor environment resolution for Canvas','Full source/parser/numeric refinement','Native filter/style lifecycle and raster semantics'],
 fullColorGrammarVerified:false,rendererRefinementVerified:false};
const output=new URL('../model/css-color-witness.json',import.meta.url),text=JSON.stringify(report,null,2)+'\n';
if(process.argv.includes('--check'))assert.equal(readFileSync(output,'utf8'),text,'CSS color witness is stale');else writeFileSync(output,text);
console.log(JSON.stringify({sources:sources.length,assignments:assignments.length,fullColorGrammarVerified:false}));

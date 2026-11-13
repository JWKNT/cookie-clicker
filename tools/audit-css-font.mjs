/** Source pins for the closed fixed-pixel Canvas font declaration model. */
import assert from'node:assert/strict';
import{readFileSync,writeFileSync}from'node:fs';
import{createHash}from'node:crypto';
import{loadGameSource}from'../model/game-source.mjs';
const paths={'canvas_rendering_context_2d.cc':'modules/canvas/canvas2d/canvas_rendering_context_2d.cc','canvas_font_cache.cc':'core/html/canvas/canvas_font_cache.cc'};
const sources=Object.entries(paths).map(([file,path])=>{const text=readFileSync(new URL(`../model/browser-source/chromium-87/${file}`,import.meta.url),'utf8');return{file,url:`https://github.com/chromium/chromium/blob/87.0.4280.141/third_party/blink/renderer/${path}`,sha256:createHash('sha256').update(text).digest('hex')};});
const native=readFileSync(new URL('../model/browser-source/chromium-87/canvas_rendering_context_2d.cc',import.meta.url),'utf8');
assert(native.includes('String CanvasRenderingContext2D::font() const'));
assert(native.includes('UpdateStyleAndLayoutTreeForNode(canvas())'));
assert(native.includes('SetComputedSize(final_description.SpecifiedSize())'));
const game=loadGameSource(),statements=game.sources['main.js'].split('\n').flatMap((line,index)=>/ctx\.font='[^']+';/.test(line)?[{line:index+1,source:line.trim()}]:[]);
assert.equal(statements.length,5);
const report={schema:1,scope:'fixed integer-pixel Canvas font shorthand and retained family data',chromiumVersion:'87.0.4280.141',sources,mainSourceHash:game.hashes['main.js'],statements,
 implementation:{grammar:'Integer px size0..1024, ordered ASCII unescaped family identifiers/strings, five base generic families, native EOF closing of a final quoted string. Invalid accepted-grammar values do not change state; other grammar remains explicit.',metadata:'Size, ordered family names, generic-vs-literal flag and original source are retained independently of getter serialization.',text:'Native normalized px size, canonical base generic names, space-containing family quoting and comma-space family list. The getter string is not used as a font-identity substitute.',state:'Canvas snapshot includes parsed font metadata and public getter text; save/restore/reset use the same stored drawing state.'},
 validation:['node lean/check_javascript_font.mjs --engine','node lean/check_javascript_canvas.mjs --engine'],
 remaining:['General font shorthand and escaped/non-ASCII family grammar','Relative/system/platform font resolution and environment-dependent description fields','Full style/layout flush and font-cache lifecycle refinement','Font loading, glyph shaping, metrics and text rasterization'],
 fontMetricsVerified:false,rendererRefinementVerified:false};
const output=new URL('../model/css-font-witness.json',import.meta.url),text=JSON.stringify(report,null,2)+'\n';
if(process.argv.includes('--check'))assert.equal(readFileSync(output,'utf8'),text,'CSS font witness is stale');else writeFileSync(output,text);
console.log(JSON.stringify({sources:sources.length,statements:statements.length,fontMetricsVerified:false}));

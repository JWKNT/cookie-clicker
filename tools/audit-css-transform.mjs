/** Native source pins for transform declaration storage/text, not geometry. */
import assert from 'node:assert/strict';
import{readFileSync,writeFileSync}from'node:fs';
import{createHash}from'node:crypto';
import{loadGameSource}from'../model/game-source.mjs';
const file='css_numeric_literal_value.cc',source=readFileSync(new URL(`../model/browser-source/chromium-87/${file}`,import.meta.url),'utf8');
assert.ok(source.includes('String::Format("%.6g%s", number, suffix)'));
assert.ok(source.includes('constexpr int kMinInteger = -999999;'));
assert.ok(source.includes('constexpr int kMaxInteger = 999999;'));
const game=loadGameSource(),main=game.sources['main.js'];
const statements=main.split('\n').flatMap((line,index)=>line.includes('Game.ascendMeter.style.transform=')||line.includes("Game.l.style.transform='scale('")?[{line:index+1,source:line.trim()}]:[]);
const report={schema:1,scope:'CSS transform declaration parsing, full numeric cache and CSSOM text',chromiumVersion:'87.0.4280.141',
 source:{file,url:`https://github.com/chromium/chromium/blob/87.0.4280.141/third_party/blink/renderer/core/css/${file}`,sha256:createHash('sha256').update(source).digest('hex')},gameSourceHash:game.hashes['main.js'],sourceStatements:statements,
 supportedFunctions:['scale','scaleX','scaleY','translate','translateX','translateY','rotate','matrix'],
 numericModel:'Finite binary64 arguments of magnitude at most1000000. Internal cache text round-trips the parsed value; CSSOM/attribute text uses the native small-integer path or nearest-even C %.6g formatting, including exponent thresholds/padding.',
 remaining:['Complete CSS tokenization and value grammar','Relative/physical length computed values and3D transforms','Native mutation/style lifecycle effects','Typed OM and computed transforms','Transform geometry, hit testing, painting and renderer refinement'],
 validation:'node lean/check_javascript_transform.mjs --engine',transformGeometryVerified:false,rendererRefinementVerified:false};
const output=new URL('../model/css-transform-witness.json',import.meta.url),text=JSON.stringify(report,null,2)+'\n';
if(process.argv.includes('--check'))assert.equal(readFileSync(output,'utf8'),text,'CSS transform witness is stale');
else writeFileSync(output,text);
console.log(JSON.stringify({statements:statements.length,transformGeometryVerified:false}));

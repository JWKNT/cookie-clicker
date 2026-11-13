/** Pinned CSS background-position token storage; no layout/raster refinement. */
import assert from 'node:assert/strict';
import {createHash} from 'node:crypto';
import {readFileSync,writeFileSync} from 'node:fs';
import {loadGameSource} from '../model/game-source.mjs';
const paths={
 'css_parser_token.cc':'core/css/parser/css_parser_token.cc',
 'css_parser_token.h':'core/css/parser/css_parser_token.h',
 'css_parsing_utils.cc':'core/css/properties/css_parsing_utils.cc',
 'css_numeric_literal_value.cc':'core/css/css_numeric_literal_value.cc'};
const sources=Object.entries(paths).map(([file,path])=>{const text=readFileSync(new URL('../model/browser-source/chromium-87/'+file,import.meta.url),'utf8');return{file,url:'https://github.com/chromium/chromium/blob/87.0.4280.141/third_party/blink/renderer/'+path,sha256:createHash('sha256').update(text).digest('hex')};});
const token=readFileSync(new URL('../model/browser-source/chromium-87/css_parser_token.cc',import.meta.url),'utf8');
assert.match(token,/clampTo<double>\(numeric_value, -std::numeric_limits<float>::max\(\),\s+std::numeric_limits<float>::max\(\)\)/);
const source=loadGameSource();
const statements=source.sources['main.js'].split('\n').flatMap((line,i)=>line.includes('Game.ascendMeter.style.backgroundPosition=')?[{line:i+1,source:line.trim()}]:[]);
assert.equal(statements.length,1);
const report={schema:1,scope:'source background-position numeric parsing, retained value and CSSOM text',sources,
 gameSourceHash:source.hashes['main.js'],sourceStatements:statements,
 supported:'One/two position components using px, percent or source keywords. Numeric tokens clamp to the finite binary32 magnitude range while retaining binary64 precision inside it. Lossless internal text is separate from the pinned CSS small-integer/%.6g getter and attribute text.',
 maximumMagnitude:{binary64Hex:'47efffffe0000000',exactInteger:'340282346638528859811704183484516925440'},
 remaining:['Relative/physical units, computed values and full invalid-value recovery','Multiple layers and three/four component grammar','CSS Typed OM and computed/used positions','Image painting, clipping and hit testing','General browser parser/renderer refinement'],
 validation:'node lean/check_javascript_background_position.mjs --engine',rendererRefinementVerified:false};
const target=new URL('../model/css-position-witness.json',import.meta.url),text=JSON.stringify(report,null,2)+'\n';
if(process.argv.includes('--check'))assert.equal(readFileSync(target,'utf8'),text,'CSS position witness is stale');else writeFileSync(target,text);
console.log(JSON.stringify({sources:sources.length,sourceStatements:statements.length,rendererRefinementVerified:false}));

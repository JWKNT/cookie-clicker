/** Pinned border grammar/default evidence; this is not a renderer refinement. */
import assert from 'node:assert/strict';
import {createHash} from 'node:crypto';
import {readFileSync,writeFileSync} from 'node:fs';
import {compilePinnedStylesheets} from '../model/css-ast.mjs';
const directory=new URL('../model/browser-source/chromium-87/',import.meta.url);
const paths={
 'css_parsing_utils.cc':'core/css/properties/css_parsing_utils.cc',
 'css_properties.json5':'core/css/css_properties.json5',
 'style_builder_converter.cc':'core/css/resolver/style_builder_converter.cc',
};
const sources=Object.entries(paths).map(([file,path])=>({file,
 url:`https://github.com/chromium/chromium/blob/87.0.4280.141/third_party/blink/renderer/${path}`,
 sha256:createHash('sha256').update(readFileSync(new URL(file,directory))).digest('hex')}));
const parser=readFileSync(new URL('css_parsing_utils.cc',directory),'utf8');
assert.match(parser,/if \(!result_width\)\s+result_width = CSSInitialValue::Create\(\);/);
const properties=readFileSync(new URL('css_properties.json5',directory),'utf8');
assert.match(properties,/name: "border-left-width",[\s\S]*?default_value: "LayoutUnit\(3\)"/);
assert.match(properties,/name: "border-left-style",[\s\S]*?default_value: "none"/);
const converter=readFileSync(new URL('style_builder_converter.cc',directory),'utf8');
assert.match(converter,/case CSSValueID::kThin:\s+result = 1;/);
assert.match(converter,/case CSSValueID::kMedium:\s+result = 3;/);
assert.match(converter,/case CSSValueID::kThick:\s+result = 5;/);
const declarations=compilePinnedStylesheets().flatMap(sheet=>sheet.rules.flatMap(rule=>rule.kind==='style'?
 rule.declarations.filter(d=>/^border(?:-(?:top|right|bottom|left))?$/.test(d.property)).map(d=>({stylesheet:sheet.name,sha256:sheet.sha256,property:d.property,start:d.start,end:d.end,important:d.important})):[]));
const report={schema:1,scope:'closed-border-shorthand-geometry',chromiumVersion:'87.0.4280.141',sources,declarations,
 initial:{widthCssPixels:3,style:'none',color:'currentColor'},keywordWidths:{thin:1,medium:3,thick:5},
 implemented:'Order-independent width/style/color parsing; nonnegative integral px widths and native width keywords; admitted fixed colors and currentColor validation; reset missing width/style to their native initial values. Geometric consumers require zoom1.',
 proof:'CookieClicker.JavaScript.Css.Border.none_keeps_medium checks that border:none retains medium width before a later style override.',
 remaining:['Fractional or relative lengths and LayoutUnit rounding','Complete CSS color grammar and CSS-wide reset/inheritance','Invalid-value cascade recovery','Border image painting and native renderer refinement'],
 validation:'node lean/check_javascript_border.mjs --engine',rendererRefinementVerified:false};
const target=new URL('../model/css-border-witness.json',import.meta.url),output=JSON.stringify(report,null,2)+'\n';
if(process.argv.includes('--check'))assert.equal(readFileSync(target,'utf8'),output,'CSS border witness is stale');
else writeFileSync(target,output);
console.log(JSON.stringify({sources:sources.length,declarations:declarations.length,rendererRefinementVerified:false}));

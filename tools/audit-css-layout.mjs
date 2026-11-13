/** Source pins for the closed CSS layout fragment, not renderer refinement. */
import assert from 'node:assert/strict';
import {createHash} from 'node:crypto';
import {readFileSync,writeFileSync} from 'node:fs';
import {compilePinnedStylesheets} from '../model/css-ast.mjs';
const directory=new URL('../model/browser-source/chromium-87/',import.meta.url);
const paths={
  'html.css':'core/html/resources/html.css',
  'element.cc':'core/dom/element.cc',
  'layout_box.cc':'core/layout/layout_box.cc',
  'ng_absolute_utils.cc':'core/layout/ng/ng_absolute_utils.cc',
  'layout_unit.h':'platform/geometry/layout_unit.h',
  'length_functions.cc':'platform/geometry/length_functions.cc',
  'document.cc':'core/dom/document.cc',
  'css_parsing_utils.cc':'core/css/properties/css_parsing_utils.cc',
};
const sources=Object.entries(paths).map(([file,path])=>({file,url:`https://github.com/chromium/chromium/blob/87.0.4280.141/third_party/blink/renderer/${path}`,sha256:createHash('sha256').update(readFileSync(new URL(file,directory))).digest('hex')}));
const ua=readFileSync(new URL('html.css',directory),'utf8'),unit=readFileSync(new URL('layout_unit.h',directory),'utf8'),element=readFileSync(new URL('element.cc',directory),'utf8');
assert.match(ua,/body\s*\{\s*display: block;\s*margin: 8px/);
assert.match(unit,/kLayoutUnitFractionalBits = 6/);
assert.match(element,/DOMRect\* Element::getBoundingClientRect\(\)/);
const stylesheets=compilePinnedStylesheets().reverse().map(({name,sha256,rules})=>({name,sha256,rules:rules.length}));
const report={schema:1,scope:'closed-source-css-cascade-and-integral-positioned-boxes',chromiumVersion:'87.0.4280.141',sources,stylesheets,
  implementation:{syntax:'Explicit token, selector, declaration, keyframe and font-face data; source ranges and order retained. Runtime style text is consumed by a closed Lean parser, without a string-to-AST lookup.',cascade:'HTML selector fragment with specificity, source order and author/inline important ranking. Unknown dynamic pseudo-class truth remains explicit.',stylesheetActivation:'Actual connected link/style order selects configured loaded source or parses actual runtime text. Unknown source, alternate/media selection and unsupported runtime grammar remain unresolved.',overflowProjection:'All possibly matching overflow declarations must be whole hidden/visible shorthands. Kernel lemmas preserve paired axis candidate lists, winners and the allowed value class under arbitrary candidate selection. Unknown pointer state is not assigned. Other dynamic geometry and axis overrides remain explicit.',geometry:'Known non-replaced block elements; definite root sizes; absolute/fixed axes with zero margins, padding and effective border; integral px and 0/100 percent lengths.',hiddenBoxes:'A positive display/all cascade query on an actual ancestor makes every descendant layout box absent. It does not parse unrelated descendant geometry or require viewport dimensions. Unknown dynamic display and all resets cannot establish this result.',range:'Inputs, containing boxes and output coordinates are restricted to ±1000000 CSS pixels. Horizontal integer percentages additionally require an exactly representable binary32 product of magnitude at most 2^24 and an integral quotient by100. General LayoutUnit quantization/saturation is not supplied.',horizontalWidth:'A separate content/padding/border-width calculation supports non-replaced normal and positioned block widths, integral box edges and min/max constraints. It requires root/body scrollbar exclusion and rejects floats, generated floats, shrink-to-fit and non-paint transitions. Paint-property transitions admit the seven native timing keywords after a nonnegative duration; functions, delays and reordered forms remain explicit. Text height is not supplied.',verticalHeight:'A separate content/padding/border-height calculation admits definite heights and positioned stretch between definite insets, with integral pixel edges and min/max constraints. It requires viewport scrollbar exclusion; content heights, percentage vertical edges and fractional LayoutUnit results remain explicit.',observations:'DOMRect allocated from computed box; measured native rectangles are never model inputs.',focus:'Inherited visibility plus a supported actual box; native focusability, scrolling and event/default actions remain separate.'},
  validation:'node lean/check_javascript_css.mjs --engine',
  remaining:['Tokenizer/parser refinement','Full browser cascade and property grammar','Font and intrinsic sizes, general normal flow, fractional layout','Transforms, scroll offsets, painting, clipping and hit testing','Stylesheet resource/load/parser timing','Complete source and native host refinement'],
  rendererRefinementVerified:false,hitTestingVerified:false};
report.implementation.editing='A separate inherited -webkit-user-modify query reads only editing/all candidates from actual ancestors. It needs no viewport or box dimensions, while unknown reset, value and selector cases remain explicit. Native SupportsFocus and style-lifecycle requirements remain separate.';
const output=new URL('../model/css-layout-witness.json',import.meta.url),text=JSON.stringify(report,null,2)+'\n';
if(process.argv.includes('--check'))assert.equal(readFileSync(output,'utf8'),text,'CSS layout witness is stale');
else writeFileSync(output,text);
console.log(JSON.stringify({sources:sources.length,stylesheets:stylesheets.length,rendererRefinementVerified:false}));

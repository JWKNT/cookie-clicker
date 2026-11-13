/** Pin the native textarea source used by the Lean value/reflection fragment. */
import assert from 'node:assert/strict';
import {createHash} from 'node:crypto';
import {readFileSync,writeFileSync} from 'node:fs';

const directory=new URL('../model/browser-source/chromium-87/',import.meta.url);
const names=['html_text_area_element.cc','html_text_area_element.idl','text_control_element.cc'];
const sources=names.map(file=>({file,
  url:`https://github.com/chromium/chromium/blob/87.0.4280.141/third_party/blink/renderer/core/html/forms/${file}`,
  sha256:createHash('sha256').update(readFileSync(new URL(file,directory))).digest('hex')}));
const area=readFileSync(new URL(names[0],directory),'utf8');
const idl=readFileSync(new URL(names[1],directory),'utf8');
const control=readFileSync(new URL(names[2],directory),'utf8');
assert(area.includes('ReplaceCRWithNewLine(normalized_value);'));
assert(area.includes('if (normalized_value == value())'));
assert(area.includes('SetNonDirtyValue(defaultValue(), TextControlSetValueSelection::kClamp);'));
assert(area.includes('DynamicTo<Text>(n)'));
assert(idl.includes('[TreatNullAs=EmptyString] DOMString value;'));
assert(idl.includes('[CEReactions, Reflect] attribute boolean readOnly;'));
assert(control.includes('GetDocument().EnqueueAnimationFrameEvent(event);'));
const report={schema:1,scope:'textarea value/reflection and cached-selection projection',
  chromiumVersion:'87.0.4280.141',sources,
  rules:{value:'Normalize CRLF and lone CR to LF; setting even an unchanged value sets the dirty flag. Changed values move the cached caret to the end.',
    defaultValue:'Concatenate direct text children; comments and nested element text do not contribute. ChildrenChanged updates nondirty value and clamps cached endpoints.',
    reflection:'readOnly, disabled and required use attribute presence and native boolean conversion; textLength counts UTF-16 code units.',
    conversion:'Actual source conversion callbacks and receiver checks; direct null value becomes empty text, while object conversion returning null becomes the string null.',
    domMutation:'Native value dependencies update on parsed-tree construction, textContent/innerHTML, insertion/removal and direct text-node changes.',
    export:'Native ExportSave supplies its current serialization as parsed readonly textarea content, then invokes focus and select. No direct save oracle is added.'},
  validation:['node lean/check_javascript_textarea.mjs --engine'],
  remaining:['Focus, selection mutation and animation-frame select-event dispatch',
    'User editing, form reset, validation, custom-element reactions and textarea cloning',
    'Style/layout/selection lifecycle and complete native form-control refinement'],
  formControlRefinementVerified:false};
const target=new URL('../model/textarea-host-witness.json',import.meta.url);
const output=JSON.stringify(report,null,2)+'\n';
if(process.argv.includes('--check'))assert.equal(readFileSync(target,'utf8'),output,'Textarea source witness is stale');
else writeFileSync(target,output);
console.log(JSON.stringify({sources:sources.length,formControlRefinementVerified:false}));

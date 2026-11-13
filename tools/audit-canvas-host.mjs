/** Pin the native implementation used by the canvas adapter, without claiming refinement. */
import assert from 'node:assert/strict';
import { createHash } from 'node:crypto';
import { readFileSync, writeFileSync } from 'node:fs';

const directory = new URL('../model/browser-source/chromium-87/',import.meta.url);
const files = {
  'html_canvas_element.cc':'third_party/blink/renderer/core/html/canvas/html_canvas_element.cc',
  'html_canvas_element.idl':'third_party/blink/renderer/core/html/canvas/html_canvas_element.idl',
  'element.cc':'third_party/blink/renderer/core/dom/element.cc',
  'html_parser_idioms.cc':'third_party/blink/renderer/core/html/parser/html_parser_idioms.cc',
  'html_canvas_element_module.idl':'third_party/blink/renderer/modules/canvas/htmlcanvas/html_canvas_element_module.idl',
  'html_canvas_element_module.cc':'third_party/blink/renderer/modules/canvas/htmlcanvas/html_canvas_element_module.cc',
  'canvas_context_creation_attributes_module.idl':'third_party/blink/renderer/modules/canvas/htmlcanvas/canvas_context_creation_attributes_module.idl',
  'canvas_context_creation_attributes_helpers.cc':'third_party/blink/renderer/modules/canvas/htmlcanvas/canvas_context_creation_attributes_helpers.cc',
  'canvas_rendering_context.cc':'third_party/blink/renderer/core/html/canvas/canvas_rendering_context.cc',
  'canvas_rendering_context_2d.cc':'third_party/blink/renderer/modules/canvas/canvas2d/canvas_rendering_context_2d.cc',
  'canvas_rendering_context_2d_settings.idl':'third_party/blink/renderer/modules/canvas/canvas2d/canvas_rendering_context_2d_settings.idl',
  'canvas_rendering_context_2d.idl':'third_party/blink/renderer/modules/canvas/canvas2d/canvas_rendering_context_2d.idl',
  'base_rendering_context_2d.cc':'third_party/blink/renderer/modules/canvas/canvas2d/base_rendering_context_2d.cc',
  'base_rendering_context_2d.h':'third_party/blink/renderer/modules/canvas/canvas2d/base_rendering_context_2d.h',
  'canvas_rendering_context_2d_state.cc':'third_party/blink/renderer/modules/canvas/canvas2d/canvas_rendering_context_2d_state.cc',
  'canvas_rendering_context_2d_state.h':'third_party/blink/renderer/modules/canvas/canvas2d/canvas_rendering_context_2d_state.h',
  'graphics_types.cc':'third_party/blink/renderer/platform/graphics/graphics_types.cc',
  'math_extras.h':'third_party/blink/renderer/platform/wtf/math_extras.h',
  'affine_transform.cc':'third_party/blink/renderer/platform/transforms/affine_transform.cc',
  'affine_transform.h':'third_party/blink/renderer/platform/transforms/affine_transform.h',
};
const sources=Object.entries(files).map(([file,path])=>({file,
  url:`https://github.com/chromium/chromium/blob/87.0.4280.141/${path}`,
  sha256:createHash('sha256').update(readFileSync(new URL(file,directory))).digest('hex')}));
const canvas=readFileSync(new URL('html_canvas_element.cc',directory),'utf8');
assert.match(canvas,/constexpr int kDefaultCanvasWidth = 300;/);
assert.match(canvas,/constexpr int kDefaultCanvasHeight = 150;/);
assert.match(canvas,/w > 0x7fffffffu/);
assert.match(canvas,/h > 0x7fffffffu/);
assert.match(readFileSync(new URL('element.cc',directory),'utf8'),/if \(value > 0x7fffffffu\)\s+value = default_value;/);
assert.match(readFileSync(new URL('html_parser_idioms.cc',directory),'utf8'),/kAcceptMinusZeroForUnsigned/);
assert.match(readFileSync(new URL('canvas_context_creation_attributes_helpers.cc',directory),'utf8'),/#if defined\(OS_MAC\)[\s\S]*?result.desynchronized = false;/);
assert.match(readFileSync(new URL('html_canvas_element_module.idl',directory),'utf8'),/PermissiveDictionaryConversion/);
const paintSource=readFileSync(new URL('base_rendering_context_2d.cc',directory),'utf8');
assert.match(paintSource,/void BaseRenderingContext2D::fillRect\(double x,[\s\S]*?ValidateRectForCanvas\(x, y, width, height\)[\s\S]*?AdjustRectForCanvas\(x, y, width, height\)/);
assert.match(readFileSync(new URL('base_rendering_context_2d.h',directory),'utf8'),/std::isfinite\(height\) && \(width \|\| height\)/);
const report={schema:5,scope:'source-pinned-canvas-adapter-not-browser-refinement',
  chromiumVersion:'87.0.4280.141',sources,
  rules:{defaultWidth:300,defaultHeight:150,maximumReflectedDimension:2147483647,
    propertyConversion:'Web IDL unsigned long, then values above INT_MAX become the dimension default before serialization',
    attributeParsing:'Leading HTML whitespace and plus accepted; negative zero accepted; first decimal digit sequence used; invalid or above INT_MAX uses dimension default',
    canvasContextMode:'none or created 2D identity; stored alpha, native prototype, canvas identity and explicit drawing-state stack; clear commands retain their matrix, and fill commands retain complete admitted drawing snapshots; pixel observations remain explicit',
    drawingState:'Native default scalar properties, save/restore, numeric and keyword setters with source coercions; unrestricted-double alpha, finite binary32 clamp for line/shadow properties, native invalid-value and signed-zero rules',
    dimensionReset:'Width/height assignment or mutation resets drawing state and clears saved states while preserving context identity and creation alpha; removing an absent attribute does not reset',
    transforms:'Pinned binary32 input clamp and binary64 affine order for scale, translate, numeric transform/setTransform, resetTransform and zero/nonfinite rotations; save/restore/reset retain matrix; ordinary bounded allocations without context loss; empty canvas operations have no paint canvas',
    fonts:'Fixed integer pixel sizes and parsed family metadata, separate from getter serialization; quoted generic-name families stay distinct; source conversion, save/restore and dimension reset retained',
    colors:'Admitted fixed CSS colors retain native RGBA bytes separately from Canvas getter formatting, including save/restore/reset; gradients, patterns and currentColor remain explicit',
    fillRect:'Actual source conversions precede finite/(width||height) validation and bounded paint allocation; native negative-rectangle adjustment and binary32 clamp; command snapshots include matrix, scalar fields, parsed colors/font and target dimensions/alpha. Initial full clip only. Zero-area calls are retained because full-canvas composite modes can affect pixels. No pixel interpretation is supplied.',
    remainingState:'Paths, nonzero C-library rotations, DOMMatrix2DInit/getTransform, font metrics and full style lifecycle, general CSS colors, filters, inherited direction, large allocation and context-loss effects remain explicit boundaries',
    contextOptionOrder:['alpha','antialias','depth','failIfMajorPerformanceCaveat','powerPreference','premultipliedAlpha','preserveDrawingBuffer','stencil','desynchronized','xrCompatible'],
    contextOptionConversion:'Actual source getters and string conversion; nonobject settings ignored; powerPreference enum validated; repeated context calls still convert options',
    platform:'macOS; pinned Chromium helper forces desynchronized false',
    twoDAttributes:'Fresh ordinary dictionary with alpha and desynchronized; color management and new Canvas2D API members absent in the captured native configuration'},
  validation:['node lean/check_javascript_browser.mjs --engine','node lean/check_javascript_canvas.mjs --engine',
    'node lean/check_javascript_canvas_matrix.mjs --engine','node lean/check_javascript_font.mjs --engine',
    'node lean/check_javascript_color.mjs --engine','node lean/check_javascript_canvas_fill.mjs --engine'],
  remaining:['Other rendering context modes and context loss','Rasterization, compositing, fonts and image decoding',
    'Canvas serialization and pixel readback','Renderer layout and full native host refinement']};
const target=new URL('../model/canvas-host-witness.json',import.meta.url), output=JSON.stringify(report,null,2)+'\n';
if(process.argv.includes('--check'))assert.equal(readFileSync(target,'utf8'),output,'Canvas source witness is stale');
else writeFileSync(target,output);
console.log(JSON.stringify({sources:sources.length,maximumReflectedDimension:report.rules.maximumReflectedDimension,fullHostRefinement:false}));

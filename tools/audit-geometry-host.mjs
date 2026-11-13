/** Pin rectangle arithmetic and bindings; no renderer-layout refinement claim. */
import assert from 'node:assert/strict';
import {createHash} from 'node:crypto';
import {readFileSync,writeFileSync} from 'node:fs';
const directory=new URL('../model/browser-source/chromium-87/',import.meta.url);
const names=['dom_rect.cc','dom_rect.h','dom_rect.idl','dom_rect_read_only.cc','dom_rect_read_only.h','dom_rect_read_only.idl','dom_rect_init.idl','geometry_util.h'];
const sources=names.map(file=>({file,url:`https://github.com/chromium/chromium/blob/87.0.4280.141/third_party/blink/renderer/core/geometry/${file}`,sha256:createHash('sha256').update(readFileSync(new URL(file,directory))).digest('hex')}));
const geometry=readFileSync(new URL('geometry_util.h',directory),'utf8'),rectangle=readFileSync(new URL('dom_rect_read_only.h',directory),'utf8');
assert.match(geometry,/std::isnan\(a\) \|\| std::isnan\(b\)/);
assert.match(geometry,/return std::min\(a, b\);/);assert.match(geometry,/return std::max\(a, b\);/);
assert.match(rectangle,/NanSafeMin\(x_, x_ \+ width_\)/);
const report={schema:1,scope:'native-rectangle-values-not-renderer-layout',chromiumVersion:'87.0.4280.141',sources,
  rules:{coordinates:'Four unrestricted binary64 values',edges:'NaN guard then C++ std::min/max of origin and origin+extent; ties retain the first operand including zero sign',constructors:'Optional undefined defaults to zero; source ToNumber callbacks run in argument order',fromRect:'Actual dictionary getter and numeric conversion order height,width,x,y',mutable:'DOMRect permits x/y/width/height setters; derived edges are readonly',intrinsics:'Native prototype references remain fixed when source overwrites constructor globals'},
  validation:'node lean/check_javascript_geometry.mjs --engine',
  remaining:['Stylesheet cascade and renderer box layout','Transforms, scrolling, font metrics and generated boxes','Host reflection and object expandos','Full native host refinement'],rendererLayoutVerified:false};
writeFileSync(new URL('../model/geometry-host-witness.json',import.meta.url),JSON.stringify(report,null,2)+'\n');
console.log(JSON.stringify({sources:sources.length,rendererLayoutVerified:false}));

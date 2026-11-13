/** Static source observer inventory for a deferred-paint relation.
 * A literal call inventory is not an alias, callback or noninterference proof. */
import assert from 'node:assert/strict';
import {readFileSync,writeFileSync} from 'node:fs';
import {compilePinnedGameAst} from '../model/javascript-ast.mjs';
const ast=compilePinnedGameAst();
const text=units=>String.fromCharCode(...units);
const property=(id,computed=false)=>{const node=ast.nodes[id];if(!computed&&node?.tag==='identifier')return node.name;if(node?.tag==='literal'&&node.literalKind==='string')return text(node.units);return null;};
const expression=(id,fuel=8)=>{if(fuel===0)return '…';const n=ast.nodes[id];if(!n)return '?';if(n.tag==='identifier')return n.name;if(n.tag==='literal')return n.raw;if(n.tag==='member')return expression(n.object,fuel-1)+(n.computed?'['+expression(n.property,fuel-1)+']':'.'+property(n.property));if(n.tag==='call')return expression(n.callee,fuel-1)+'('+n.arguments.map(i=>expression(i,fuel-1)).join(',')+')';if(n.tag==='binary')return '('+expression(n.left,fuel-1)+' '+n.operator+' '+expression(n.right,fuel-1)+')';if(n.tag==='unary')return n.operator+' '+expression(n.argument,fuel-1);return '['+n.tag+']';};
const observedNames=['getTransform','setTransform','resetTransform','getImageData','putImageData','toDataURL','toBlob','isPointInPath','isPointInStroke','measureText','rotate','drawImage','getContext'];
const where=node=>({unitName:ast.units[node.source.unit].name,unitKind:ast.units[node.source.unit].kind,origin:ast.units[node.source.unit].origin,...node.source});
const calls=[],dynamicMemberCalls=[];
for(const node of ast.nodes){if(node.tag!=='call')continue;const callee=ast.nodes[node.callee];if(callee?.tag!=='member')continue;const name=property(callee.property,callee.computed);if(callee.computed&&name===null)dynamicMemberCalls.push({node:node.id,callee:expression(node.callee),...where(node)});if(observedNames.includes(name))calls.push({method:name,receiver:expression(callee.object),arguments:node.arguments.map(i=>expression(i)),...where(node)});}
const counts=Object.fromEntries(observedNames.map(name=>[name,calls.filter(c=>c.method===name).length]));
assert.equal(counts.getTransform,0);assert.equal(counts.toDataURL,0);assert.equal(counts.getImageData,3);assert.equal(counts.putImageData,1);
const unresolvedTemplates=ast.generatedHandlers.filter(h=>h.status!=='compiled').map(h=>({status:h.status,source:h.source,event:h.event,parseError:h.parseError??null}));
const report={schema:1,scope:'literal source canvas calls and deferred-paint obligations',sourceHashes:ast.sourceHashes,
 coverage:{units:ast.units.length,includesParsedInlineAndLiteralHandlers:true,uncompiledGeneratedHandlerTemplates:unresolvedTemplates.length,
  pointsToAnalysisComplete:false,dynamicCallResolutionComplete:false},counts,calls,dynamicMemberCalls,unresolvedTemplates,
 firstLiveRotation:{file:'main.js',line:15384,expression:'(r/360)*Math.PI*2',rExpression:'Math.floor((Game.T*0.5)%360)',
  diagnosticFrame:2,diagnosticR:1,diagnosticAngleBits:'4580687790476533049',nativeLibraryResultSubstituted:false},
 deferredPaint:{status:'proposed relation; executable model still stops at nonzero rotation',
  representation:['Ordered transform operations with their converted binary64 arguments','Save/restore snapshots of transform expression and complete drawing state','Paint commands with state and canvas dimensions at invocation','Image readiness/dimensions/origin state; canvas-source content snapshot at drawImage invocation','Reset/reallocation and context-loss state'],
  mustExecute:['Native receiver branding and required-argument checks','Source coercion callbacks, source exceptions and argument order','Any source-observable native exception and resource event','Native reads/writes of exposed drawing-state properties','Pixel/metric queries or explicit unresolved requests when their semantics are not supplied'],
  mustNotAssume:['V8 Math.sin/cos equals the engine C-library functions','A later canvas source can replace its call-time snapshot','No literal getTransform means no possible observation through aliases or generated handlers','A public screenshot observation can be discarded from the policy class','Canvas dimensions and command loops do not consume source randomness'],
  obligations:['Define an exact denotation parameterized by the pinned native transform/raster functions, or a proved larger host relation for a lower bound.',
   'Prove source steps commute with the representation relation, including native validation, reset, drawing state and exception order.',
   'Discharge actual source alias/call reachability before asserting that a context has no scalar/pixel observer.',
   'Keep YouCustomizer getImageData/putImageData and text metric paths explicit until their exact interpretation is available.',
   'Provide observation and action simulations; source-economic-state equality alone does not preserve the strategy class.']},
 sourceNoninterferenceProved:false,rendererRefinementVerified:false,optimalityProved:false};
const target=new URL('../model/canvas-observer-audit.json',import.meta.url),output=JSON.stringify(report,null,2)+'\n';
if(process.argv.includes('--check'))assert.equal(readFileSync(target,'utf8'),output,'Canvas observer audit is stale');else writeFileSync(target,output);
console.log(JSON.stringify({units:ast.units.length,counts,dynamicMemberCalls:dynamicMemberCalls.length,uncompiledGeneratedHandlerTemplates:unresolvedTemplates.length,sourceNoninterferenceProved:false}));

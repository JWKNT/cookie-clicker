/** Fixed-pixel Canvas font serialization; no font metrics or text raster oracle. */
import assert from'node:assert/strict';
import{fileURLToPath}from'node:url';
import{spawnSyncWithFileInput as spawnSync}from'./process-input.mjs';
import{runNativeBrowser}from'../model/native-browser.mjs';
import{loadGameSource}from'../model/game-source.mjs';
if(!process.argv.includes('--engine'))throw new Error('Font comparisons require isolated pinned Chromium');
const cases=[],add=(source,expectedStatus)=>cases.push({source,...(expectedStatus?{expectedStatus}:{})});
for(const size of [0,1,9,10,14,20,32,255,1024])for(const family of ['Merriweather','serif','SERIF','sans-serif','cursive','fantasy','monospace','Times New Roman','"Times New Roman"',"'serif'",'"A,B"','Arial_Black','a1','"123"','" A  B "','A\tB','serif, Arial','"serif",monospace'])add(size+'px '+family);
for(const value of ['-0px Arial','-000px serif',"20px 'A B",' 020PX Merriweather ','20px\tMerriweather','20px\nArial\tBlack','20px "A\tB"','20px "A\'B"',"20px 'A\"B'",'20px A--B','20px _font','20px --font'])add(value);
for(const value of ['', 'null','undefined','inherit','initial','unset','revert','normal','bold','-1px Arial','20px','px Arial','20px 123','20px -1name','20px ,Arial','20px Arial,','20px "unterminated','20px "a"b"','20px initial','20px inherit','20px unset','20px revert','20px default'])add(value);
for(const value of ['menu','caption','bold 20px Arial','italic 20px Arial','small-caps 20px Arial','20pt Arial','20.5px Arial','+20px Arial','10000px Arial','20px/2 Arial','20px ""','20px -webkit-body','20px -webkit-test','20px system-ui','20px emoji','20px A initial','20px \\41 rial','20px /*x*/Arial','20px 汉字'])add(value,'unresolved');
const main=loadGameSource().sources['main.js'];
for(const match of main.matchAll(/\.font='([^']+)'/g))add(match[1]);
const worker=function(cases){var context=document.createElement('canvas').getContext('2d');return cases.map(function(test){if(test.expectedStatus)return{status:test.expectedStatus};context.font='17px CodecAuditMarker';context.font=test.source;return context.font==='17px CodecAuditMarker'?{status:'invalid'}:{status:'complete',text:context.font};});};
const native=runNativeBrowser(worker.toString(),cases);
const child=spawnSync(fileURLToPath(new URL('.lake/build/bin/jscsscheck',import.meta.url)),[],{input:JSON.stringify(cases.map(c=>({operation:'font',source:c.source}))),encoding:'utf8',timeout:120000,maxBuffer:8*1024*1024});
if(child.error)throw child.error;assert.equal(child.status,0,child.stderr);const observed=JSON.parse(child.stdout),failures=[];
for(let i=0;i<cases.length;i++)try{if(cases[i].expectedStatus)assert.equal(observed[i].status,cases[i].expectedStatus);else assert.deepEqual(observed[i],native.result[i]);}catch(error){failures.push({source:cases[i].source,observed:observed[i],expected:native.result[i],error:error.message});}
if(failures.length){console.error(JSON.stringify(failures,null,2));process.exitCode=1;}
console.log(JSON.stringify({cases:cases.length,passed:cases.length-failures.length,nativeComparisons:cases.filter(c=>!c.expectedStatus).length,versions:native.versions,executableHash:native.executableHash,fontMetricsVerified:false,rendererRefinementVerified:false}));

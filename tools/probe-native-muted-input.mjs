/** Finite reference execution; this is not a proof of physical-input refinement.
 * Reads only pinned source/assets, uses a new profile, and never runs steam.js. */
import {copyFileSync,cpSync,mkdirSync,mkdtempSync,readdirSync,readFileSync,rmSync,symlinkSync,writeFileSync} from 'node:fs';
import {dirname,join} from 'node:path';
import {tmpdir} from 'node:os';
import {fileURLToPath,pathToFileURL} from 'node:url';
import {createHash} from 'node:crypto';
import {spawnSync} from 'node:child_process';
import {loadGameSource} from '../model/game-source.mjs';
import {inspectNativeEngine,nativeEnginePath} from '../model/native-engine.mjs';
const hash=x=>createHash('sha256').update(x).digest('hex');
const source=loadGameSource(), identity=inspectNativeEngine();
const directory=mkdtempSync(join(tmpdir(),'cookie-muted-input-'));
const contents=join(directory,'Cookie Clicker.app','Contents'),entry=join(contents,'Resources','app');
const output=join(directory,'result.json'),fixture=join(directory,'fixture'),manifest=[];
const destination=process.argv[2]||fileURLToPath(new URL('../model/native-muted-input-witness.json',import.meta.url));
try {
 mkdirSync(join(contents,'MacOS'),{recursive:true});mkdirSync(entry,{recursive:true});
 const installedContents=dirname(dirname(nativeEnginePath()));
 copyFileSync(nativeEnginePath(),join(contents,'MacOS','Cookie Clicker'));
 copyFileSync(join(installedContents,'Info.plist'),join(contents,'Info.plist'));
 mkdirSync(join(contents,'Frameworks'));
 for(const name of readdirSync(join(installedContents,'Frameworks'))){
  const original=join(installedContents,'Frameworks',name),target=join(contents,'Frameworks',name);
  if(name.endsWith(' Helper.app')||/ Helper \((GPU|Plugin|Renderer)\)\.app$/.test(name))cpSync(original,target,{recursive:true});
  else if(name.endsWith('.framework'))symlinkSync(original,target,'dir');else throw Error('Unknown framework '+name);
 }
 const add=(relative,bytes,expected)=>{
  const sha256=hash(bytes);if(expected&&sha256!==expected)throw Error('Hash mismatch '+relative);
  const file=join(fixture,relative);mkdirSync(dirname(file),{recursive:true});writeFileSync(file,bytes);
  manifest.push({path:relative,sha256,bytes:bytes.length});
 };
 for(const [name,text] of Object.entries(source.sources))if(name!=='index.html')add('src/'+name,Buffer.from(text),source.hashes[name]);
 for(const asset of JSON.parse(readFileSync(new URL('../model/game-assets.json',import.meta.url))).assets)
  add('src/'+asset.path,readFileSync(join(source.directory,asset.path)),asset.sha256);
 add('src/style.css',readFileSync(join(source.directory,'style.css')));
 for(const name of ['fonts.css','Merriweather-Black.ttf'])add('steam/'+name,readFileSync(join(source.directory,'../steam',name)));
 const omitted='<script src="../steam/steam.js"></script>';
 if(source.sources['index.html'].split(omitted).length!==2)throw Error('Expected one Steam wrapper');
 // Explicit configured-English environment, before the unmodified source starts.
 // This supplies no game save and alters no Game field.
 const setup="<script>if(localStorage.length!==0)throw Error('Nonfresh audit profile');localStorage.setItem('CookieClickerLang','EN');</script>";
 const html=source.sources['index.html'].replace(omitted,'').replace('<head>','<head>'+setup);
 add('src/index.html',Buffer.from(html));
 const page=pathToFileURL(join(fixture,'src/index.html')).href;
 const allowed=manifest.map(x=>pathToFileURL(join(fixture,x.path)).href);
 writeFileSync(join(entry,'package.json'),JSON.stringify({name:'cookie-muted-input-audit',version:'1.0.0',main:'audit.cjs'}));
 writeFileSync(join(entry,'configuration.json'),JSON.stringify({directory,output,entry,allowed,page}));
 const bootstrap=readFileSync(new URL('./native-muted-input-worker.cjs',import.meta.url),'utf8');
 writeFileSync(join(entry,'audit.cjs'),bootstrap);
 const env={...process.env};delete env.ELECTRON_RUN_AS_NODE;
 const child=spawnSync(join(contents,'MacOS','Cookie Clicker'),[],{env,encoding:'utf8',timeout:120000,maxBuffer:8*1024*1024});
 let result;try{result=JSON.parse(readFileSync(output,'utf8'))}catch(e){throw Error('Native worker failed '+JSON.stringify({status:child.status,signal:child.signal,error:child.error,stderr:child.stderr}),{cause:e})}
 if(child.status!==0||result.error)throw Error(result.error||child.stderr);
 const receipt={schema:1,description:'Finite native trusted browser input witness; not a Lean physical-action refinement theorem',identity,sourceHashes:source.hashes,fixtureHashes:manifest,originalIndexHash:source.hashes['index.html'],steamWrapperExecuted:false,gameSourceExecuted:true,playerSaveRead:false,configuredEnglish:true,network:'only exact copied fixture URLs, data/about; external requests denied',settingsMutation:'native range input handlers only; no Game field assignments',inputMechanism:'Electron webContents.sendInputEvent',...result};
 receipt.reproduction='node tools/probe-native-muted-input.mjs';
 receipt.limitations=[
  'The initial Options click runs PlaySound before muting. The muted theorem does not remove that audio transition.',
  'This finite native run does not prove pointer targeting, input scheduling, range default actions or Steam-wrapper behavior.',
  'The copied index omits steam.js and selects English before startup. No game save is supplied.',
  'The Lean muted-body proof assumes its entry environment; initialized closure correspondence remains open.',
  'Source parsing, source reachability and browser refinement remain separate proof obligations.',
 ];
 writeFileSync(destination,JSON.stringify(receipt,null,2)+'\n');console.log(JSON.stringify({destination,initial:result.initial,muted:result.muted,final:{...result.final,events:result.final.events.length},blocked:result.blocked,errors:result.errors}));
}finally{rmSync(directory,{recursive:true,force:true})}

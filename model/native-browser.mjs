import { copyFileSync, cpSync, existsSync, mkdirSync, mkdtempSync, readdirSync, readFileSync, rmSync, symlinkSync, writeFileSync } from 'node:fs';
import { dirname, join } from 'node:path';
import { tmpdir } from 'node:os';
import { pathToFileURL } from 'node:url';
import { spawnSync } from 'node:child_process';
import { createHash } from 'node:crypto';
import vm from 'node:vm';
import { inspectNativeEngine, nativeEnginePath } from './native-engine.mjs';

/** Run a DOM comparison in an isolated copy of the installed Chromium engine.
 * The bundle has its own audit entry and profile. It never loads the installed
 * app/ directory, game entry point, Steam integration or player saves. Only the
 * native executable and engine Frameworks are reused. External requests fail.
 * `functionSource` runs in a renderer with no Node integration and gets JSON data.
 */
export function runNativeBrowser(functionSource, input, { timeout = 120000, allowEval = false, allowDataAssets = false, allowInlineStyles = false, allowInlineScripts = false, documentMode = 'data', captureConsoleEvents = false, inputSequence = [], afterInputFunctionSource = null } = {}) {
  if (!Array.isArray(inputSequence) || inputSequence.length > 1000) throw new Error('Invalid finite input sequence');
  for (const event of inputSequence) {
    if (!['mouseMove','mouseDown','mouseUp'].includes(event.type) || !Number.isInteger(event.x) || !Number.isInteger(event.y) || event.x < -2147483648 || event.x > 2147483647 || event.y < -2147483648 || event.y > 2147483647 ||
        !['left','right','middle'].includes(event.button ?? 'left') ||
        (event.modifiers !== undefined && (!Array.isArray(event.modifiers) || event.modifiers.some(value => !['leftButtonDown','middleButtonDown','rightButtonDown','shift','control','alt','meta'].includes(value)))) ||
        !Number.isInteger(event.clickCount ?? 1) || (event.clickCount ?? 1) < 0 || (event.clickCount ?? 1) > 3 ||
        Object.keys(event).some(key => !['type','x','y','button','clickCount','modifiers'].includes(key))) throw new Error('Invalid isolated mouse input');
  }
  if ((inputSequence.length || afterInputFunctionSource !== null) && typeof afterInputFunctionSource !== 'string') throw new Error('Mouse input needs a result reader');
  if (!['data', 'file'].includes(documentMode)) throw new Error('Audit document mode must be data or file');
  if (process.platform !== 'darwin') throw new Error('The isolated native-browser audit currently requires the installed macOS engine');
  const identity = inspectNativeEngine();
  const installedBinary = nativeEnginePath();
  const installedContents = dirname(dirname(installedBinary));
  const directory = mkdtempSync(join(tmpdir(), 'cookie-clicker-dom-audit-'));
  // Electron 11 derives helper bundle names from the outer bundle basename.
  const contents = join(directory, 'Cookie Clicker.app', 'Contents');
  const resources = join(contents, 'Resources');
  const entry = join(resources, 'app');
  const executable = join(contents, 'MacOS', 'Cookie Clicker');
  const output = join(directory, 'result.json');
  try {
    mkdirSync(join(contents, 'MacOS'), { recursive: true });
    mkdirSync(entry, { recursive: true });
    copyFileSync(installedBinary, executable);
    const executableHash = createHash('sha256').update(readFileSync(executable)).digest('hex');
    const frameworks = join(contents, 'Frameworks');
    mkdirSync(frameworks);
    for (const name of readdirSync(join(installedContents, 'Frameworks'))) {
      const original = join(installedContents, 'Frameworks', name);
      if (name.endsWith(' Helper.app') || / Helper \((GPU|Plugin|Renderer)\)\.app$/.test(name)) {
        cpSync(original, join(frameworks, name), { recursive: true });
      } else if (name.endsWith('.framework')) symlinkSync(original, join(frameworks, name), 'dir');
      else throw new Error(`Unexpected installed engine Frameworks entry: ${name}`);
    }
    // Native signing binds the executable to this metadata. The audit entry
    // sets its own app name/profile before ready; no installed app entry exists
    // in this temporary Resources directory.
    const plist = readFileSync(join(installedContents, 'Info.plist'), 'utf8');
    writeFileSync(join(contents, 'Info.plist'), plist);
    writeFileSync(join(entry, 'package.json'), JSON.stringify({ name: 'cookie-clicker-model-dom-audit', version: '1.0.0', main: 'audit.cjs' }));
    writeFileSync(join(directory, 'request.json'), JSON.stringify({ functionSource, input, inputSequence, afterInputFunctionSource }));
    const scriptSources=[...(allowEval?["'unsafe-eval'"]:[]),...(allowInlineScripts?["'unsafe-inline'"]:[])];
    const documentHtml = `<!doctype html><meta http-equiv="Content-Security-Policy" content="default-src 'none'; style-src ${allowInlineStyles ? "'unsafe-inline'" : "'none'"}${scriptSources.length ? '; script-src '+scriptSources.join(' ') : ''}${allowDataAssets ? '; img-src data:; media-src data:' : ''}"><title>Isolated DOM audit</title><body></body>`;
    const documentPath = join(directory, 'document.html');
    if (documentMode === 'file') writeFileSync(documentPath, documentHtml);
    const documentUrl = documentMode === 'file' ? pathToFileURL(documentPath).href : 'data:text/html;charset=utf-8,' + encodeURIComponent(documentHtml);
    const bootstrap = `
const fs=require('fs'),path=require('path'),electron=require('electron');
const {app,BrowserWindow,session}=electron;
const directory=${JSON.stringify(directory)},entry=${JSON.stringify(entry)},output=${JSON.stringify(output)};
const mark=stage=>fs.writeFileSync(output+'.stage',stage);mark('bootstrap');
app.setName('Cookie Clicker Model DOM Audit');
app.setPath('userData',path.join(directory,'profile'));
app.setPath('cache',path.join(directory,'cache'));
app.disableHardwareAcceleration();
app.commandLine.appendSwitch('disable-background-networking');
app.commandLine.appendSwitch('disable-component-update');
app.commandLine.appendSwitch('disable-domain-reliability');
app.commandLine.appendSwitch('disable-sync');
app.commandLine.appendSwitch('enable-features','NetworkServiceInProcess');
function fail(error){fs.writeFileSync(output,JSON.stringify({error:String(error&&error.stack||error)}));app.exit(1);}
process.on('uncaughtException',fail);process.on('unhandledRejection',fail);
app.on('child-process-gone',(event,details)=>fail(new Error('Audit child exited: '+JSON.stringify(details))));
app.whenReady().then(async()=>{
 mark('ready');
 if(fs.realpathSync(app.getAppPath())!==fs.realpathSync(entry)||fs.realpathSync(process.resourcesPath)!==fs.realpathSync(path.dirname(entry)))throw new Error('Unexpected native audit app path');
 if(app.dock)app.dock.hide();
 session.defaultSession.setPermissionRequestHandler((webContents,permission,callback)=>callback(false));
 session.defaultSession.webRequest.onBeforeRequest((details,callback)=>callback({cancel:!details.url.startsWith('data:')&&!details.url.startsWith('about:')&&details.url!==${JSON.stringify(documentUrl)}}));
 const window=new BrowserWindow({show:false,width:800,height:600,webPreferences:{nodeIntegration:false,contextIsolation:true,sandbox:false,backgroundThrottling:false}});
 mark('window-created');
 window.webContents.on('render-process-gone',(event,details)=>fail(new Error('Audit renderer exited: '+JSON.stringify(details))));
 window.webContents.on('did-fail-load',(event,code,description)=>fail(new Error('Audit document load failed: '+code+' '+description)));
 window.webContents.on('will-navigate',event=>event.preventDefault());
 window.webContents.on('new-window',event=>event.preventDefault());
 await window.loadURL(${JSON.stringify(documentUrl)});
 mark('document-loaded');
 const consoleEvents=[];
 if(${JSON.stringify(captureConsoleEvents)}){
  window.webContents.debugger.attach('1.3');
  window.webContents.debugger.on('message',(event,method,parameters)=>{
   if(method==='Runtime.consoleAPICalled')consoleEvents.push({type:parameters.type,args:parameters.args});
  });
  await window.webContents.debugger.sendCommand('Runtime.enable');
  consoleEvents.length=0;
 }
 const request=JSON.parse(fs.readFileSync(path.join(directory,'request.json'),'utf8'));
 const evaluated=await window.webContents.executeJavaScript('(async()=>{try{return {ok:true,value:await ('+request.functionSource+')('+JSON.stringify(request.input)+')}}catch(error){return {ok:false,error:{name:error.name,message:error.message,stack:error.stack}}}})()',false);
 if(!evaluated.ok)throw new Error('Renderer comparison failed: '+JSON.stringify(evaluated.error));
 let result=evaluated.value;
 for(const event of request.inputSequence){
  window.webContents.sendInputEvent(event);
  await window.webContents.executeJavaScript('void 0',false);
 }
 if(request.afterInputFunctionSource!==null){
  const after=await window.webContents.executeJavaScript('(async()=>{try{return {ok:true,value:await ('+request.afterInputFunctionSource+')()}}catch(error){return {ok:false,error:{name:error.name,message:error.message,stack:error.stack}}}})()',false);
  if(!after.ok)throw new Error('Renderer input result failed: '+JSON.stringify(after.error));
  result=after.value;
 }
 if(${JSON.stringify(captureConsoleEvents)})await window.webContents.debugger.sendCommand('Runtime.evaluate',{expression:'void 0'});
 mark('comparison-complete');
 const renderer=await window.webContents.executeJavaScript('({userAgent:navigator.userAgent})',false);
 fs.writeFileSync(output,JSON.stringify({result,renderer,consoleEvents,versions:process.versions,appPath:app.getAppPath(),resourcesPath:process.resourcesPath,userData:app.getPath('userData'),gameEntryPointExecuted:false,externalNetworking:false,auditConfiguration:{networkServiceInProcess:true,hardwareAcceleration:false,nodeIntegration:false,contextIsolation:true,rendererSandbox:false,allowEval:${JSON.stringify(allowEval)},allowDataAssets:${JSON.stringify(allowDataAssets)},allowInlineStyles:${JSON.stringify(allowInlineStyles)},allowInlineScripts:${JSON.stringify(allowInlineScripts)},documentMode:${JSON.stringify(documentMode)},captureConsoleEvents:${JSON.stringify(captureConsoleEvents)},inputSequence:${JSON.stringify(inputSequence)},trustedInputSource:${JSON.stringify(inputSequence.length ? "Electron webContents.sendInputEvent in isolated window" : null)}}}));
 window.destroy();app.exit(0);
}).catch(fail);
`;
    new vm.Script(bootstrap, { filename: 'audit.cjs' });
    writeFileSync(join(entry, 'audit.cjs'), bootstrap);
    const environment = { ...process.env };
    delete environment.ELECTRON_RUN_AS_NODE;
    const child = spawnSync(executable, [], { env: environment, encoding: 'utf8', timeout, maxBuffer: 8 * 1024 * 1024 });
    if (child.error) throw new Error(`Native DOM worker process failed at ${existsSync(output + '.stage') ? readFileSync(output + '.stage', 'utf8') : 'before-bootstrap'}: ${child.error.message}; ${child.stderr}`, { cause: child.error });
    let result;
    try { result = JSON.parse(readFileSync(output, 'utf8')); }
    catch (error) { throw new Error(`Native DOM worker produced no result (status=${child.status}, signal=${child.signal}): ${child.stderr}`, { cause: error }); }
    if (child.status !== 0 || result.error) throw new Error(`Native DOM worker failed: ${result.error || child.stderr}`);
    return { ...result, identity, executableHash };
  } finally {
    rmSync(directory, { recursive: true, force: true });
  }
}

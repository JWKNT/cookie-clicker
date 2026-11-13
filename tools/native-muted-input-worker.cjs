const fs=require('fs'),path=require('path'),{app,BrowserWindow,session}=require('electron');
const {directory,output,entry,allowed:allowedUrls,page}=JSON.parse(fs.readFileSync(path.join(__dirname,'configuration.json'),'utf8'));
app.setName('Cookie Muted Input Audit');app.setPath('userData',path.join(directory,'profile'));app.setPath('cache',path.join(directory,'cache'));
app.disableHardwareAcceleration();app.commandLine.appendSwitch('disable-background-networking');app.commandLine.appendSwitch('disable-component-update');app.commandLine.appendSwitch('disable-sync');app.commandLine.appendSwitch('enable-features','NetworkServiceInProcess');
function fail(e){fs.writeFileSync(output,JSON.stringify({error:String(e.stack||e)}));app.exit(1)}
process.on('uncaughtException',fail);process.on('unhandledRejection',fail);
app.whenReady().then(async()=>{
 if(fs.realpathSync(app.getAppPath())!==fs.realpathSync(entry))throw Error('Wrong entry');
 if(app.dock)app.dock.hide();
 const allowed=new Set(allowedUrls),blocked=[];
 session.defaultSession.setPermissionRequestHandler((w,p,c)=>c(false));
 session.defaultSession.webRequest.onBeforeRequest((d,c)=>{const u=d.url.split(/[?#]/)[0],ok=allowed.has(u)||d.url.startsWith('data:')||d.url.startsWith('about:');if(!ok)blocked.push(d.url);c({cancel:!ok})});
 const w=new BrowserWindow({show:false,width:1280,height:900,webPreferences:{nodeIntegration:false,contextIsolation:true,sandbox:false,backgroundThrottling:false}});
 w.webContents.on('will-navigate',e=>e.preventDefault());w.webContents.on('new-window',e=>e.preventDefault());
 w.webContents.on('render-process-gone',(e,d)=>fail(Error(JSON.stringify(d))));
 const errors=[];w.webContents.on('console-message',(e,l,m)=>{if(l>=2)errors.push(m)});
 await w.loadURL(page);
 const read=src=>w.webContents.executeJavaScript(src,false);
 await read(`new Promise((resolve,reject)=>{const start=Date.now();let timer=setInterval(()=>{if(typeof Game==='object'&&Game.ready&&Game.T>=3){clearInterval(timer);resolve(true)}else if(Date.now()-start>60000){clearInterval(timer);reject(Error('Game readiness timeout'))}},20)})`);
 const initial=await read(`({App:App,version:Game.version,volume:Game.volume,cookies:Game.cookies,cookieClicks:Game.cookieClicks,onMenu:Game.onMenu,T:Game.T,language:localStorage.getItem('CookieClickerLang'),savePresent:!!localStorage.getItem('CookieClickerGame')})`);
 if(initial.App!==0||initial.cookies!==0||initial.cookieClicks!==0||initial.savePresent)throw Error('Unexpected initial state '+JSON.stringify(initial));
 await read(`window.auditInputEvents=[];for(const type of ['pointerdown','pointerup','mousedown','mouseup','click','input','change'])document.addEventListener(type,e=>{const target=e.target;window.auditInputEvents.push({type,target:target.id||target.parentNode&&target.parentNode.id||target.nodeName,isTrusted:e.isTrusted,detail:e.detail,value:target.value,volume:Game.volume,cookies:Game.cookies})},false)`);
 const actions=[];
 const mouse=async(type,x,y)=>{const event={type,x,y,button:'left',clickCount:1,...(type==='mouseDown'?{modifiers:['leftButtonDown']}: {})};actions.push(event);w.webContents.sendInputEvent(event);await read('void 0')};
 const click=async(id,left=false)=>{
  const p=await read(`(()=>{const el=document.getElementById(${JSON.stringify(id)}),r=el.getBoundingClientRect();const x=Math.round(${left?'r.left+2':'r.left+r.width/2'}),y=Math.round(r.top+r.height/2);const hit=document.elementFromPoint(x,y);if(hit!==el&&!el.contains(hit))throw Error('Target obscured: '+el.id+' by '+(hit&&hit.id));return {id:el.id,x,y,rect:{left:r.left,top:r.top,width:r.width,height:r.height},hit:hit.id||hit.nodeName}})()`);
  actions.push({target:p});await mouse('mouseMove',p.x,p.y);await mouse('mouseDown',p.x,p.y);await mouse('mouseUp',p.x,p.y);
 };
 await click('prefsButton');
 const prefs=await read(`({menu:Game.onMenu,volume:Game.volume,slider:document.getElementById('volumeSlider').outerHTML,cookies:Game.cookies})`);
 await click('volumeSlider',true);
 const muted=await read(`({menu:Game.onMenu,volume:Game.volume,slider:document.getElementById('volumeSlider').value,cookies:Game.cookies})`);
 if(muted.volume!==0||muted.cookies!==0)throw Error('Native slider did not mute: '+JSON.stringify(muted));
 await click('bigCookie');
 const final=await read(`({volume:Game.volume,cookies:Game.cookies,cookiesEarned:Game.cookiesEarned,handmadeCookies:Game.handmadeCookies,cookieClicks:Game.cookieClicks,menu:Game.onMenu,T:Game.T,events:window.auditInputEvents,activeElement:document.activeElement.id,scrollX:window.scrollX,scrollY:window.scrollY})`);
 if(final.cookieClicks!==1||final.cookies!==1||final.volume!==0)throw Error('Cookie click result '+JSON.stringify(final));
 fs.writeFileSync(output,JSON.stringify({initial,prefs,muted,final,actions,blocked,errors,versions:process.versions,appPath:app.getAppPath(),userData:app.getPath('userData')}));w.destroy();app.exit(0);
}).catch(fail);

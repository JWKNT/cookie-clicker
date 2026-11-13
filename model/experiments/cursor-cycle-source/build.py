"""Build the archived inspector against a compatible, already built repository.
This writes only OUTPUT. It does not rebuild or modify repository dependencies.
"""
from pathlib import Path
import argparse,hashlib,json,os,shlex,shutil,subprocess
parser=argparse.ArgumentParser()
parser.add_argument('repository',type=Path)
parser.add_argument('output',type=Path)
parser.add_argument('--check-only',action='store_true')
args=parser.parse_args()
bundle=Path(__file__).resolve().parent
root=args.repository.resolve()/'lean'
out=args.output.resolve()
identity=json.loads((bundle/'dependency-sources.json').read_text())
for item in identity['requiredSourceFiles']:
 source=args.repository.resolve()/item['path']
 if hashlib.sha256(source.read_bytes()).hexdigest()!=item['sha256']:
  raise SystemExit('Dependency source differs: '+item['path'])
compile_trace=root/'.lake/build/ir/JavaScriptAstMain.c.o.export.trace'
response=root/'.lake/build/bin/jsastcheck.rsp'
if not compile_trace.is_file() or not response.is_file():
 raise SystemExit('First run LEAN_NUM_THREADS=2 lake build jsastcheck in REPOSITORY/lean')
if args.check_only:
 print('Source pins and build inputs match. No files changed.');raise SystemExit(0)
out.mkdir(parents=True,exist_ok=True)
local=out/'lean'
(local/'CookieClicker').mkdir(parents=True,exist_ok=True)
for p in (root/'.lake/build/lib/lean/CookieClicker').glob('*.olean'):
 q=local/'CookieClicker'/p.name
 if not q.exists() and not q.is_symlink():q.symlink_to(p)
modules=['CookieClicker.JavaScriptCursorCycleSyntax','CookieClicker.JavaScriptCursorCycleTrace','CycleAstMain']
env={**os.environ,'LEAN_NUM_THREADS':'1','LEAN_PATH':str(local)+':'+str(root/'.lake/build/lib/lean')}
compiler=shlex.split(json.loads(compile_trace.read_text())['log'][0]['message'][3:])
objects=[]
for module in modules:
 relative=Path(*module.split('.')).with_suffix('.lean')
 source=local/relative;shutil.copy2(bundle/'source'/relative,source)
 olean=source.with_suffix('.olean')
 if olean.is_symlink():olean.unlink()
 c=out/(module.replace('.','_')+'.c');obj=c.with_suffix('.o')
 subprocess.run(['lean','--root='+str(local),'-o',str(olean),'-c',str(c),str(source)],cwd=root,env=env,check=True)
 command=compiler.copy();i=command.index('-o');command[i+1]=str(obj);command[i+2]=str(c)
 subprocess.run(command,cwd=root,check=True);objects.append(obj)
lines=response.read_text().splitlines()
lines=[line for line in lines if 'JavaScriptAstMain.c.o.export' not in line and 'CookieClicker/JavaScriptCursorCycleSyntax.c.o.export' not in line]
lines=['"'+str(obj)+'"' for obj in objects]+lines
rsp=out/'cycle-driver.rsp';rsp.write_text('\n'.join(lines)+'\n')
executable=out/'cycle-driver'
subprocess.run([compiler[0],'-o',str(executable),'@'+str(rsp)],cwd=root,check=True)
print(json.dumps({'status':'built','executable':str(executable),'sha256':hashlib.sha256(executable.read_bytes()).hexdigest()}))

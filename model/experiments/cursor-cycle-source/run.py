"""Run the exact archived diagnostic, using a regular file for standard input.
A process error or time limit is censored evidence, never a game transition.
"""
from pathlib import Path
import argparse,gzip,hashlib,json,resource,subprocess,sys,time
parser=argparse.ArgumentParser()
parser.add_argument('executable',type=Path)
parser.add_argument('output',type=Path)
parser.add_argument('--timeout-seconds',type=int,default=600)
args=parser.parse_args()
if args.timeout_seconds<=0:raise SystemExit('Timeout must be positive')
bundle=Path(__file__).resolve().parent
out=args.output.resolve();out.mkdir(parents=True,exist_ok=True)
request=gzip.decompress((bundle/'request.json.gz').read_bytes())
expected='52fb65af37571ac769cdc90d8d3841917250d47f0af4fe4e3c6c3edec906a5aa'
if hashlib.sha256(request).hexdigest()!=expected:raise SystemExit('Archived request hash differs')
request_path=out/'request.json';request_path.write_bytes(request)
executable=args.executable.resolve()
receipt={'requestSha256':expected,'executableSha256':hashlib.sha256(executable.read_bytes()).hexdigest(),
 'arguments':['--execute'],'budgetSeconds':args.timeout_seconds,'physicalInputRefined':False,
 'universalAcceptanceProved':False,'fundedFixture':True,'finalStateAvailable':False}
start=time.monotonic();before=resource.getrusage(resource.RUSAGE_CHILDREN)
with request_path.open('rb') as inp,(out/'result.json').open('wb') as result,(out/'stderr.log').open('wb') as err:
 process=subprocess.Popen([str(executable),'--execute'],stdin=inp,stdout=result,stderr=err)
 try:
  code=process.wait(timeout=args.timeout_seconds)
  receipt.update(status='returned' if code==0 else 'process-error',exitCode=code,finalStateAvailable=code==0)
 except subprocess.TimeoutExpired:
  process.kill();process.wait();receipt.update(status='censored',reason='process-wall-time-budget')
after=resource.getrusage(resource.RUSAGE_CHILDREN)
receipt.update(seconds=time.monotonic()-start,cpuSeconds=after.ru_utime+after.ru_stime-before.ru_utime-before.ru_stime,
 peakResidentBytes=after.ru_maxrss*(1 if sys.platform=='darwin' else 1024))
if receipt['finalStateAvailable']:
 result=json.loads((out/'result.json').read_text())[0]
 receipt['interpreterStatus']=result.get('status')
 receipt['cycleStatus']=result.get('cursorCycleReport',{}).get('status')
(out/'run.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt,indent=2))
if receipt.get('cycleStatus')!='accepted':raise SystemExit(1)

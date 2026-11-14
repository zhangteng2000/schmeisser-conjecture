"""Generate and independently replay the complete finite scalar range.

Ordinary local multiprocessing; no agent delegation.
"""
import argparse,concurrent.futures,hashlib,json,time
from pathlib import Path
from certify_mass_scalar_v4 import run
from verify_mass_scalar_integer_v4 import verify

def worker(pair):
 lo,hi=pair
 p=run(lo,hi,quiet=True,folder='mass_scalar_v4_certificates')
 r=verify(p['certificate'],quiet=True) if p['PASS'] else None
 return dict(N_range=list(pair),primary=p,independent=r)

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--workers',type=int,default=4);args=ap.parse_args()
 ranges=[(j,j) for j in range(3,129)];lo=129
 while lo<=5999:
  hi=min(5999,max(lo,int(lo*1.03)-1));ranges.append((lo,hi));lo=hi+1
 pending=list(ranges);passed=[];failed=[];active={};start=time.time();last=start
 frozen={name:hashlib.sha256((Path('work')/name).read_bytes()).hexdigest() for name in ['certify_mass_scalar_v4.py','verify_mass_scalar_integer_v4.py','mass_arb_helpers.py','mass_integer_arithmetic.py']}
 pool=concurrent.futures.ProcessPoolExecutor(max_workers=args.workers)
 try:
  while pending or active:
   while pending and len(active)<args.workers:
    pair=pending.pop(0);active[pool.submit(worker,pair)]=pair
   done,_=concurrent.futures.wait(active,timeout=20,return_when=concurrent.futures.FIRST_COMPLETED)
   for f in done:
    pair=active.pop(f)
    try:row=f.result()
    except Exception as exc:
     failed.append(dict(N_range=pair,error=repr(exc)));print(json.dumps({'ERROR':pair,'error':repr(exc)}),flush=True);continue
    if not row['primary']['PASS']:
     if pair[0]<pair[1]:
      mid=(pair[0]+pair[1])//2;pending=[(pair[0],mid),(mid+1,pair[1])]+pending
      print(json.dumps({'SPLIT':pair,'unresolved':row['primary']['unresolved'],'pending':row['primary']['pending']}),flush=True)
     else:failed.append(row);print(json.dumps({'PRIMARY_FAILED':pair}),flush=True)
    elif not row['independent']['PASS']:
     failed.append(row);print(json.dumps({'INDEPENDENT_FAILED':pair,'detail':row['independent']}),flush=True)
    else:
     passed.append(row);print(json.dumps({'PASS':pair,'nodes':row['primary']['nodes'],'leaves':row['primary']['leaves'],'generation_seconds':row['primary']['seconds'],'replay_seconds':row['independent']['seconds']}),flush=True)
   state=dict(initial_ranges=ranges,passed=[r['N_range'] for r in passed],active=list(active.values()),queued=pending,failed=failed,complete=not pending and not active and not failed,seconds=time.time()-start,frozen_sources=frozen)
   Path('work/mass_scalar_v4_batch_state.json').write_text(json.dumps(state,indent=2))
   Path('work/mass_scalar_v4_batch_passes.json').write_text(json.dumps(passed,indent=2))
   if time.time()-last>30:
    print(json.dumps({'passed_ranges':len(passed),'active':list(active.values()),'queued':len(pending),'failed':len(failed),'seconds':time.time()-start}),flush=True);last=time.time()
 finally:
  if active:
   for p in pool._processes.values():p.terminate()
  pool.shutdown(wait=True,cancel_futures=True)
 for name,expected in frozen.items():
  if hashlib.sha256((Path('work')/name).read_bytes()).hexdigest()!=expected:raise ValueError('source changed while running: '+name)
 print(json.dumps({'COMPLETE':not failed,'passed_ranges':len(passed),'failed':len(failed),'seconds':time.time()-start}),flush=True)

if __name__=='__main__':main()

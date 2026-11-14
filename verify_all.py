"""Portable, standard-library-only replay of the delivered proof package.

Run without Python optimization: python verify_all.py --workers 4
The original certificate and receipt files are never modified.
"""
import argparse,concurrent.futures,hashlib,json,os,shutil,sys,tempfile,time
from pathlib import Path

def need(value,message):
 if not value:raise ValueError(message)
def sha(path):return hashlib.sha256(Path(path).read_bytes()).hexdigest()
def read(path):return json.loads(Path(path).read_text(encoding='utf8'))
def inside(base,relative):
 path=(base/relative).resolve()
 need(path.is_relative_to(base),'path outside package')
 return path

def worker(args):
 root,source,destination,row=args
 sys.path.insert(0,str(Path(root)/'work'))
 from verify_mass_scalar_integer_v4 import verify
 shutil.copyfile(source,destination)
 result=verify(destination,quiet=True)
 need(result['PASS'],'integer inequality failed')
 for key in ['N_range','nodes','leaves','certificate_sha256']:
  need(result[key]==row[key],'replay record mismatch: '+key)
 return {key:result[key] for key in ['N_range','nodes','leaves','seconds']}

def main():
 need(__debug__,'Python -O/-OO is not allowed: assertions must remain active')
 ap=argparse.ArgumentParser(description=__doc__)
 ap.add_argument('--workers',type=int,default=4)
 ap.add_argument('--report',type=Path)
 args=ap.parse_args();need(1<=args.workers<=64,'invalid worker count')
 root=Path(__file__).resolve().parent;start=time.time()
 digests={}
 for line in (root/'SHA256SUMS.txt').read_text(encoding='utf8').splitlines():
  digest,relative=line.split('  ',1)
  need(relative not in digests,'duplicate checksum entry')
  need(sha(inside(root,relative))==digest,'checksum mismatch: '+relative)
  digests[relative]=digest
 need('verify_all.py' in digests,'launcher checksum missing')
 manifest=read(root/'work/mass_proof_manifest.json')
 need(manifest['status']=='PASS' and manifest['N_range']==[3,5999],'manifest scope')
 for name,digest in manifest['frozen_sources'].items():
  need(digests['work/'+name]==digest,'source provenance: '+name)
 need(digests['work/assemble_mass_proof.py']==manifest['assembler_sha256'],'assembler provenance')
 sys.path.insert(0,str(root/'work'))
 import uniform_large_degree_constants as constants
 need(constants.result==manifest['constant_checks'],'exact constants differ')
 need(constants.result['checks']==33,'constant count')
 next_N=3;expected_nodes=expected_leaves=0;tasks=[]
 with tempfile.TemporaryDirectory(prefix='schmeisser-integer-replay-') as temporary:
  for row in manifest['ranges']:
   lo,hi=row['N_range']
   need(type(lo) is int and type(hi) is int and lo==next_N and lo<=hi<=5999,'degree gap or overlap')
   next_N=hi+1
   need(digests[row['certificate']]==row['certificate_sha256'],'certificate provenance')
   for key in ['primary_receipt','integer_receipt']:
    need(digests[row[key]]==row[key+'_sha256'],'receipt provenance')
   receipt=read(inside(root,row['integer_receipt']))
   need(receipt['PASS'],'original integer receipt not PASS')
   for key in ['N_range','nodes','leaves','certificate_sha256']:
    need(receipt[key]==row[key],'original integer receipt differs')
   need(receipt['verifier_sha256']==manifest['frozen_sources']['verify_mass_scalar_integer_v4.py'],'receipt verifier')
   need(receipt['arithmetic_dependency_sha256']==manifest['frozen_sources']['mass_integer_arithmetic.py'],'receipt kernel')
   expected_nodes+=row['nodes'];expected_leaves+=row['leaves']
   tasks.append((str(root),str(inside(root,row['certificate'])),str(Path(temporary)/Path(row['certificate']).name),row))
  need(next_N==6000 and len(tasks)==manifest['range_count']==261,'degree coverage incomplete')
  need(manifest['integer_degrees']==5997,'degree count')
  need(expected_nodes==manifest['nodes'] and expected_leaves==manifest['leaves'],'total counts')
  need(expected_nodes+len(tasks)==2*expected_leaves,'forest count')
  print(json.dumps({'checksums':'PASS','files':len(digests),'constants':'PASS','checks':33,'ranges':len(tasks)}),flush=True)
  results=[];last=time.time()
  with concurrent.futures.ProcessPoolExecutor(max_workers=args.workers) as pool:
   futures=[pool.submit(worker,t) for t in tasks]
   for future in concurrent.futures.as_completed(futures):
    results.append(future.result())
    if time.time()-last>=20:
     print(json.dumps({'replayed':len(results),'of':len(tasks),'seconds':time.time()-start}),flush=True);last=time.time()
  need(len(results)==len(tasks),'missing replay result')
 result=dict(status='PASS',scope='all finite N=3..5999 certificates plus 33 exact constant checks; analytic arguments are in the manuscript',
     ranges=len(results),nodes=expected_nodes,leaves=expected_leaves,constant_checks=33,
     checksum_files=len(digests),seconds=time.time()-start,python=sys.version,
     manifest_sha256=sha(root/'work/mass_proof_manifest.json'),
     ranges_replayed=sorted(results,key=lambda r:r['N_range']))
 if args.report:
  destination=args.report.resolve()
  need(destination not in [inside(root,p) for p in digests],'report would overwrite a verified input')
  destination.write_text(json.dumps(result,indent=2),encoding='utf8')
 print(json.dumps({k:result[k] for k in ['status','ranges','nodes','leaves','constant_checks','seconds']}),flush=True)

if __name__=='__main__':main()

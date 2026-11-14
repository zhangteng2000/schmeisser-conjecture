"""Audit finite degree coverage, transcript structure and frozen provenance.

Arithmetic acceptance is in the separate pure-integer replay. This script
also produces the numerical summary included in the mathematical manuscript.
"""
import gzip,hashlib,json
from collections import Counter
from pathlib import Path

W=Path('work')
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def read(p):return json.loads(Path(p).read_text(encoding='utf8'))
def need(v,msg):
 if not v:raise ValueError(msg)

def tree(path):
 nodes=leaves=0;counts=Counter();stack=[(0.,1.)]
 with gzip.open(path,'rt',encoding='utf8') as f:
  header=json.loads(next(f));need(header['format']=='mass-scalar-tree-v4','format')
  need(header['u_edges']==[0.0.hex(),1.0.hex()],'root domain')
  for line in f:
   p=line.strip().split()
   if p==['END']:
    need(not stack and not f.read().strip(),'unfinished or trailing transcript');break
   need(bool(stack),'too many nodes');a,b=stack.pop();nodes+=1
   if p[0]=='S':
    need(len(p)==2,'split syntax');m=float.fromhex(p[1]);need(a<m<b,'split position')
    stack.extend([(m,b),(a,m)])
   else:
    need(len(p)==2 and p[0]=='L','leaf syntax');leaves+=1;counts[p[1]]+=1
  else:raise ValueError('missing END')
 need(nodes+1==2*leaves,'binary-tree count')
 return header,nodes,leaves,dict(counts)

def main():
 state=read(W/'mass_scalar_v4_batch_state.json')
 need(state['complete'] and not state['failed'] and not state['active'] and not state['queued'],'batch incomplete')
 frozen=state['frozen_sources']
 for name,value in frozen.items():need(sha(W/name)==value,'changed source '+name)
 data=sorted(read(W/'mass_scalar_v4_batch_passes.json'),key=lambda r:r['N_range'])
 need(len(data)==len(state['passed']),'batch count mismatch')
 rows=[];next_N=3;total=Counter();categories=Counter()
 for row in data:
  lo,hi=row['N_range'];need(type(lo) is int and type(hi) is int and lo==next_N and lo<=hi<=5999,'degree gap/overlap')
  next_N=hi+1;p=row['primary'];r=row['independent'];need(p['PASS'] and r['PASS'],'unverified range')
  path=W/'mass_scalar_v4_certificates'/f'N_{lo}_{hi}.tree.gz'
  digest=sha(path);h,nodes,leaves,counts=tree(path)
  need(h['N_range']==[lo,hi] and h['precision_bits']==112,'header range/precision')
  need(h['source_sha256']==frozen['certify_mass_scalar_v4.py'],'header source')
  need(h['dependencies']=={'mass_arb_helpers.py':frozen['mass_arb_helpers.py']},'header dependency')
  need(p['source_sha256']==h['source_sha256'] and p['dependencies']==h['dependencies'],'primary provenance')
  need(r['verifier_sha256']==frozen['verify_mass_scalar_integer_v4.py'],'verifier provenance')
  need(r['arithmetic_dependency_sha256']==frozen['mass_integer_arithmetic.py'] and r['precision_bits']==192,'integer kernel provenance')
  for log in [p,r]:
   need(log['N_range']==[lo,hi] and log['certificate_sha256']==digest,'receipt range/hash')
   need(log['nodes']==nodes and log['leaves']==leaves and log['counts']==counts,'receipt tree counts')
  need(p['pending']==0 and not p['unresolved'],'unresolved primary')
  primary=path.with_name(f'N_{lo}_{hi}.json');independent=path.with_name(f'N_{lo}_{hi}.integer.json')
  need(read(primary)==p and read(independent)==r,'stored receipt differs')
  rows.append(dict(N_range=[lo,hi],certificate=path.as_posix(),certificate_sha256=digest,
       primary_receipt=primary.as_posix(),primary_receipt_sha256=sha(primary),
       integer_receipt=independent.as_posix(),integer_receipt_sha256=sha(independent),nodes=nodes,leaves=leaves))
  total.update(nodes=nodes,leaves=leaves)
  for tag,count in counts.items():
   if ':' in tag:tag='base_damping' if tag.startswith('24576:') else 'exact_polar_refinement'
   categories[tag]+=count
 need(next_N==6000,'finite endpoint missing')
 constants=read(W/'uniform_large_degree_constants.json')
 need(constants['status']=='PASS' and constants['checks']==33,'constant checks')
 need(constants['source_sha256']==sha(W/'uniform_large_degree_constants.py'),'constant source changed')
 result=dict(status='PASS',scope='complete finite scalar exclusion, with independent analytic endpoints in the manuscript',
     N_range=[3,5999],integer_degrees=5997,range_count=len(rows),nodes=total['nodes'],leaves=total['leaves'],
     categories=dict(categories),frozen_sources=frozen,constant_checks=constants,
     assembler_sha256=sha(__file__),ranges=rows)
 dest=W/'mass_proof_manifest.json';dest.write_text(json.dumps(result,indent=2),encoding='utf8')
 groups=[]
 for lo,hi in [(3,19),(20,128),(129,5999)]:
  selected=[r for r in rows if lo<=r['N_range'][0] and r['N_range'][1]<=hi]
  groups.append((lo,hi,len(selected),sum(r['nodes'] for r in selected),sum(r['leaves'] for r in selected)))
 out=[r'\begin{proposition}[已完成的有限验证]',
      r'对每个整数 $3\le N\le5999$，两参数必要条件不可能同时成立。',r'\end{proposition}',
      r'\noindent\textbf{计算记录。}全部区间均完成生成与独立整数重放，汇总如下。',
      r'\begin{center}\begin{tabular}{rrrr}\toprule',r'$N$ 范围 & 次数区间数 & 分割树节点数 & 叶区间数\\\midrule']
 for lo,hi,k,n,l in groups:out.append(f'${lo}\\text{{--}}{hi}$ & {k} & {n} & {l}\\\\')
 out.extend([r'\midrule',f'合计 & {len(rows)} & {total["nodes"]} & {total["leaves"]}\\\\',
             r'\bottomrule\end{tabular}\end{center}',
             r'每棵树恰好覆盖 $[0,1]$；次数区间的并集恰为 $3,4,\ldots,5999$，无缺口或重叠。',
             r'另有 $33$ 项精确有理常数比较全部通过。完整哈希与逐区间记录见随附包的',
             r'\texttt{work/mass\_proof\_manifest.json}。',
             r'独立整数复核器的 SHA-256 为',
             r'\begin{center}\ttfamily '+frozen['verify_mass_scalar_integer_v4.py'][:32]+r'\\',
             frozen['verify_mass_scalar_integer_v4.py'][32:]+r'\end{center}'])
 (W/'mass_certificate_summary.tex').write_text('\n'.join(out)+'\n',encoding='utf8')
 print(json.dumps({k:result[k] for k in ['status','N_range','integer_degrees','range_count','nodes','leaves','categories']}))

if __name__=='__main__':main()

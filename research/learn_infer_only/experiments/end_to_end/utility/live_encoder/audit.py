"""Independently reconstruct the four live outputs from original cached features."""
from pathlib import Path
import hashlib,json
import numpy as np
ROOT=Path(__file__).resolve().parent;UTILITY=ROOT.parent
BASE=UTILITY.parents[1]/'adaptation_utility'
load=lambda p:json.loads(Path(p).read_text())
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()

def main():
    report=load(ROOT/'results/run_001/report.json');records=load(BASE/'representation_records.json')
    hidden=np.load(BASE/'representation_features.npz')['mean_10'].astype(np.float64)
    reference=np.column_stack([hidden,np.ones(384)])
    for route in [0,1]:
        teacher=[r['id'] for r in records if r['pool']=='teach' and r['skill']==route]
        ids=[r['id'] for r in records if r['skill']==route]
        reference[ids,:-1]-=hidden[teacher].mean(0)
        reference[ids]/=np.linalg.norm(reference[teacher],axis=1).max()
    expected=np.clip(np.rint(127*reference),-127,127).astype(np.int64)
    for path,h in report['source_sha256'].items():assert sha(path)==h
    assert [r['record_id'] for r in report['commands']]==[0,64,256,320]
    checks=0
    for row in report['commands']:
        assert row['exit_code']==0 and row['encoder_result']['cached_quantized_comparison']
        cmd=row['command'];rid=row['record_id']
        input_path=Path(cmd[cmd.index('--input')+1]);output_path=Path(cmd[cmd.index('--output')+1])
        assert load(input_path)=={'text':records[rid]['text'],'route':records[rid]['skill'],'label':1}
        assert sha(input_path)==row['input_sha256'] and sha(output_path)==row['vector_sha256']
        assert load(output_path)==expected[rid].tolist();checks+=len(expected[rid])
        assert input_path.stat().st_mode&0o777==output_path.stat().st_mode&0o777==0o600
        assert row['max_rss_bytes_macos']>0 and all(v>=0 for v in row['time_command'].values())
    assert checks==2308
    result={'passed':True,'model_records':4,'independent_exact_integer_agreements':checks,
       'original_sources_unchanged':True,'all_private_input_output_modes':'0600','script_sha256':sha(__file__),
       'live_report_sha256':sha(ROOT/'results/run_001/report.json'),
       'scope':'Four specified texts; equality of quantized vectors, not all-text or all-batch numerical equivalence'}
    (ROOT/'audit.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))

if __name__=='__main__':main()

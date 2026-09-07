"""Write authorized issuer-only vectors and public query vectors from frozen data."""
from pathlib import Path
import hashlib,json,os
from build_mapping import ROOT,ENC,FIXTURE_SHA,sha,load,save,vdigest

def private_json(path,value):
    descriptor=os.open(path,os.O_WRONLY|os.O_CREAT|os.O_TRUNC,0o600)
    with os.fdopen(descriptor,'w') as stream:json.dump(value,stream,separators=(',',':'));stream.write('\n')
    os.chmod(path,0o600)

def main():
    assert sha(ENC/'fixture.txt')==FIXTURE_SHA
    mapping=load(ROOT/'issuer_oracle/mapping.json')
    lines=(ENC/'fixture.txt').read_text().splitlines()
    private=ROOT/'issuer_oracle/vectors';private.mkdir(exist_ok=True,mode=0o700);os.chmod(private,0o700)
    public=ROOT/'public_queries';public.mkdir(exist_ok=True)
    issued=[];public_queries={};oracle={};hashes={}
    for e in mapping['events']:
        row=lines[e['source_fixture_line']-1].split();vector=list(map(int,row[6:]))
        assert len(vector)==577
        if e['kind']=='Learn':
            assert row[0]=='L' and vdigest(vector)==e['contribution_sha256']
            path=private/(e['event_id']+'.json');private_json(path,vector)
            issued.append({'event_id':e['event_id'],'kind':'Learn','route':e['route'],'issuer_vector_path':str(path)})
        else:
            assert row[0]=='Q' and vdigest(vector)==e['query_vector_sha256']
            if e['record_id'] not in public_queries:
                path=public/f"q{len(public_queries):02d}.json";save(path,vector);public_queries[e['record_id']]=path
            else:path=public_queries[e['record_id']];assert load(path)==vector
            issued.append({'event_id':e['event_id'],'kind':'Infer','route':e['route'],'public_query_vector_path':str(path)})
            oracle[e['event_id']]={'expected_scalar':e['expected_score'],'sign':e['expected_sign'],
              'target_label':e['target_label'],'correct':e['correct'],'public_structural_zero':e['public_structural_zero']}
        hashes[str(path)]=sha(path)
    assert len(issued)==480 and len(public_queries)==16 and len(oracle)==96
    for path in private.glob('*.json'):assert path.stat().st_mode&0o777==0o600
    private_json(ROOT/'issuer_oracle/input_index.json',{'schema':'E2E_ISSUER_INPUT_INDEX_V1',
       'exposure':'Issuer/coordinator only; never pass index or issuer vectors to host/authority roles','events':issued})
    private_json(ROOT/'issuer_oracle/expected_scalars.json',{'schema':'E2E_TEST_ORACLE_SCALARS_V1',
       'exposure':'Test oracle only; never a host/authority input','queries':oracle})
    save(ROOT/'materialized_inputs_manifest.json',{'passed':True,'script_sha256':sha(__file__),
       'mapping_sha256':sha(ROOT/'issuer_oracle/mapping.json'),'issuer_vector_count':384,
       'public_query_vector_count':16,'oracle_count':96,'files_sha256':hashes,
       'private_index_sha256':sha(ROOT/'issuer_oracle/input_index.json'),
       'oracle_sha256':sha(ROOT/'issuer_oracle/expected_scalars.json'),
       'all_issuer_vector_modes':'0600','private_vector_directory_mode':'0700',
       'scope':'Local data-flow segregation; shared Unix account still defeats role isolation'})
    print(json.dumps({'passed':True,'issuer_vectors':384,'public_query_vectors':16,'oracle_queries':96,
                     'private_index':str(ROOT/'issuer_oracle/input_index.json')},indent=2))

if __name__=='__main__':main()

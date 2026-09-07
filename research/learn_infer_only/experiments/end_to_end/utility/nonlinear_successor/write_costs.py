"""Render the frozen cost measurements as four-column, LF-only CSV.

Reads existing experiment results; does not rerun fitting, encoding or utility.
The earlier hand-rendered CSV is preserved byte-for-byte under historical/.
"""
from pathlib import Path
import csv,hashlib,json
ROOT=Path(__file__).resolve().parent

def main():
    preparation=json.loads((ROOT/'preparation.json').read_text())
    results=json.loads((ROOT/'results.json').read_text())
    selected=results['selected_quadratic'];rank=int(selected.removeprefix('quadratic'))
    dimension=preparation['dimensions'][selected]
    encoding=preparation['encodings'][selected]['cost'];fit=preparation['pca_fit_cost']
    policy_coefficients=2*(576+576*rank+rank+(dimension-1)+1)
    rows=[
      ('source_encoder','backbone',0,'executed forward calls; cached mean10 only; no forward in this study'),
      ('issuer_or_public_query','center_embedding',576,'scalar subtractions'),
      ('issuer_or_public_query','PCA_projection',576*rank,'public-coefficient scalar products'),
      ('issuer_or_public_query','PCA_reduction',rank*575,'scalar additions'),
      ('issuer_or_public_query','component_standardization',rank,'public divisions/scalings'),
      ('issuer_or_public_query','unique_degree2_products',rank*(rank+1)//2,'source-feature products'),
      ('issuer_or_public_query','transformed_centering',dimension-1,'scalar subtractions'),
      ('issuer_or_public_query','norm_scaling',dimension,'public divisions/scalings'),
      ('issuer_or_public_query','round_and_clip',dimension,'nearest-even rounding and clipping'),
      ('issuer_only','observed_label_multiply',dimension,'scalar sign multiplications'),
      ('public_policy','selected_calibration_per_two_routes',policy_coefficients,'float64 coefficients; excludes serialization metadata'),
      ('public_policy','selected_calibration_payload',8*policy_coefficients,'bytes atfloat64; selected transform only'),
      ('resident','dimension_after_public_zero_padding',577,'coordinates; unchanged contract'),
      ('resident','route_capacity',32,'original contributions per route'),
      ('resident','universal_abs_score_bound',577*32*127*127,'integer; unchanged signed range'),
      ('measurement','PCA_fit_wall',fit['wall_seconds'],'seconds for2route SVDs'),
      ('measurement','PCA_fit_CPU',fit['cpu_seconds'],'process CPUseconds'),
      ('measurement','PCA_fit_highwater_RSS',fit['process_high_water_rss_bytes_macos'],'bytes; whole process, not incremental'),
      ('measurement',selected+'_encode_wall',encoding['wall_seconds'],'seconds for384 cached vectors'),
      ('measurement',selected+'_encode_CPU',encoding['cpu_seconds'],'process CPUseconds'),
      ('measurement',selected+'_encode_highwater_RSS',encoding['process_high_water_rss_bytes_macos'],'bytes; whole process, not incremental'),
      ('measurement','full_evaluation_wall',results['cost']['wall_seconds'],'seconds includes independent integer audits'),
      ('measurement','full_evaluation_CPU',results['cost']['cpu_seconds'],'process CPUseconds'),
      ('measurement','full_evaluation_highwater_RSS',results['cost']['process_high_water_rss_bytes_macos'],'bytes; whole process, not incremental'),
    ]
    assert all(len(row)==4 for row in rows)
    output=ROOT/'costs.csv'
    with output.open('w',newline='') as stream:
        writer=csv.writer(stream,lineterminator='\n')
        writer.writerow(['role','operation','quantity','unit_and_scope']);writer.writerows(rows)
    raw=output.read_bytes();assert b'\r' not in raw
    print(json.dumps({'rows_including_header':len(rows)+1,'columns':4,'line_endings':'LF',
      'costs_sha256':hashlib.sha256(raw).hexdigest(),'utility_rerun':False}))

if __name__=='__main__':main()

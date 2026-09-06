#!/usr/bin/env python3
"""Independently validate saved estimator aggregation; no estimators are run."""
from collections import Counter
from datetime import datetime, timezone
import ast
import hashlib
import json
import math
from pathlib import Path
import sys

HERE=Path(__file__).resolve().parent
EST=HERE.parents[1]/'experiments/he_closure_costs/estimator'


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def identity(row):
    return tuple(row[k] for k in ['Q_bits_label','samples','model','attack'])


def numeric_expression(text):
    """Interpret only scalar arithmetic in Sage's printed cost; never eval code."""
    def visit(node):
        if isinstance(node,ast.Expression):return visit(node.body)
        if isinstance(node,ast.Constant) and isinstance(node.value,(int,float)):return float(node.value)
        if isinstance(node,ast.Name) and node.id=='e':return math.e
        if isinstance(node,ast.UnaryOp) and isinstance(node.op,ast.USub):return -visit(node.operand)
        if isinstance(node,ast.UnaryOp) and isinstance(node.op,ast.UAdd):return visit(node.operand)
        if isinstance(node,ast.BinOp):
            a,b=visit(node.left),visit(node.right)
            if isinstance(node.op,ast.Add):return a+b
            if isinstance(node.op,ast.Sub):return a-b
            if isinstance(node.op,ast.Mult):return a*b
            if isinstance(node.op,ast.Div):return a/b
            if isinstance(node.op,ast.Pow):return a**b
        raise ValueError('Unsupported scalar cost expression: '+text)
    return visit(ast.parse(text.replace('^','**'),mode='eval'))


def main():
    started=datetime.now(timezone.utc).isoformat()
    manifest_path=EST/'artifact_manifest.json'
    manifest=json.loads(manifest_path.read_text())
    file_matches={row['path']:digest(Path(row['path']))==row['sha256'] for row in manifest['files']}
    assert all(file_matches.values()), [p for p,ok in file_matches.items() if not ok]
    summary_path=EST/'summary.json'
    summary=json.loads(summary_path.read_text())
    inputs={str(manifest_path):digest(manifest_path),str(summary_path):digest(summary_path),str(Path(__file__)):digest(Path(__file__))}
    rows=[]
    files=[]
    for spec in summary['input_results']:
        path=EST/spec['file']
        data=path.read_bytes()
        inputs[str(path)]=hashlib.sha256(data).hexdigest()
        assert inputs[str(path)]==spec['sha256']
        parsed=[dict(json.loads(line),source_file=spec['file']) for line in data.splitlines()]
        assert len(parsed)==spec['rows']
        assert dict(Counter(r['status'] for r in parsed))==spec['status_counts']
        rows+=parsed
        files.append({'file':spec['file'],'rows':len(parsed),'status_counts':spec['status_counts']})
    q_values={'83':2199023190017*4398046486529,'109':68719403009*68719230977*137438822401}
    for row in rows:
        assert int(row['Q_exact'])==q_values[row['Q_bits_label']]
        assert row['n']==4096 and row['Xs']==row['Xe']=='CenteredBinomial(20)'
        if row['status']=='EXECUTED' and isinstance(row.get('log2_fields',{}).get('rop'),(int,float)):
            assert abs(math.log2(numeric_expression(row['fields']['rop']))-row['log2_fields']['rop'])<1e-6
    lattice=[r for r in rows if r['attack'] not in ['bkw','arora_gb']]
    assert len({identity(r) for r in lattice})==len(lattice)
    primary=[r for r in lattice if r['model']!='MATZOV_quantum_depth_width']
    assert len(primary)==72 and all(r['status']=='EXECUTED' for r in primary)
    selected=[]
    for item in summary['lattice_summary']:
        group=[r for r in lattice if all(r[k]==item[k] for k in ['Q_bits_label','samples','model'])]
        good=[r for r in group if r['status']=='EXECUTED' and isinstance(r.get('log2_fields',{}).get('rop'),(int,float))]
        best=min(good,key=lambda r:r['log2_fields']['rop'])
        assert item['best_completed_lattice_attack']==best['attack']
        assert item['selected_result_file']==best['source_file']
        assert item['log2_estimated_cost']==best['log2_fields']['rop']
        names={'usvp','bdd','dual','dual_hybrid'}
        if item['model']!='MATZOV_quantum_depth_width':names|={'bdd_hybrid','bdd_mitm_hybrid'}
        assert item['coverage_complete_for_named_suite']==(names<={r['attack'] for r in good})
        selected.append({k:item[k] for k in ['Q_bits_label','samples','model','best_completed_lattice_attack','log2_estimated_cost','coverage_complete_for_named_suite']})
    matches=[]; recovered=[]; unresolved=[]
    for spec in summary['isolated_verification']:
        path=EST/spec['result_file'];inputs[str(path)]=digest(path)
        row=json.loads(path.read_text())
        prior=next(r for r in lattice if identity(r)==identity(row))
        if row['status']=='EXECUTED' and prior['status']=='EXECUTED':
            assert row['log2_fields']['rop']==prior['log2_fields']['rop']
            matches.append(identity(row))
        elif row['status']=='EXECUTED':recovered.append(identity(row))
        else:unresolved.append(identity(row))
    assert len(matches)==16 and len(recovered)==3 and len(unresolved)==1
    # A reusable finite-sample attack caps the best available infinite-sample proxy.
    reused=[]
    for row in selected:
        if row['samples']=='infinity':
            finite=next(r for r in selected if r['samples']=='4096' and r['Q_bits_label']==row['Q_bits_label'] and r['model']==row['model'])
            reused.append({'Q_bits_label':row['Q_bits_label'],'model':row['model'],
                'literal_infinity_optimizer_output':row['log2_estimated_cost'],
                'available_cost_using_finite_sample_reuse':min(row['log2_estimated_cost'],finite['log2_estimated_cost'])})
    result={'label':'EXECUTED independent saved-result aggregation and manifest audit; no HE or estimator rerun',
        'command':[sys.executable,str(Path(__file__).resolve())],'started_utc':started,
        'inputs':inputs,'inputs_unchanged':all(digest(Path(p))==h for p,h in inputs.items()),
        'artifact_manifest_files_verified':len(file_matches),'result_files':files,
        'primary_completed_lattice_rows':len(primary),'selected':selected,
        'exact_fresh_process_rechecks':len(matches),'recovered_fresh_process_failures':recovered,
        'unresolved_fresh_process_failures':unresolved,'finite_sample_reuse':reused,
        'scope':'Model-specific heuristic work estimates; no all-attacks bound, ring reduction, or post-quantum theorem'}
    (HERE/'he_results_review.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:result[k] for k in ['inputs_unchanged','artifact_manifest_files_verified','primary_completed_lattice_rows','exact_fresh_process_rechecks','unresolved_fresh_process_failures']},indent=2))


if __name__=='__main__':main()

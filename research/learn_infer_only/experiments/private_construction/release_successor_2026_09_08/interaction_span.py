#!/usr/bin/env python3
"""Public arithmetic only: reachability of diagonal bilinear output probes."""
import hashlib
import json
from pathlib import Path

HERE=Path(__file__).resolve().parent
REGISTRY=HERE.parent/'public_setup_pq/ring_seed_semantic_successor/registry.json'

def main():
    raw=REGISTRY.read_bytes()
    assert hashlib.sha256(raw).hexdigest()=='295c8feed3bc299e0a97f15b36808fdba1e85e03c3d234e6253d136a5b4778b5'
    registry=json.loads(raw)
    rows=[entry['vector'] for entry in registry['queries']]
    p=registry['p'];dimension=registry['dimension']
    pivots=[];matrix=[[v%p for v in row] for row in rows]
    rank=0
    for column in range(dimension):
        pivot=next((i for i in range(rank,len(matrix)) if matrix[i][column]),None)
        if pivot is None:continue
        matrix[rank],matrix[pivot]=matrix[pivot],matrix[rank]
        inverse=pow(matrix[rank][column],-1,p)
        matrix[rank]=[(v*inverse)%p for v in matrix[rank]]
        for i in range(len(matrix)):
            if i!=rank and matrix[i][column]:
                factor=matrix[i][column]
                matrix[i]=[(a-factor*b)%p for a,b in zip(matrix[i],matrix[rank])]
        pivots.append(column);rank+=1
        if rank==len(matrix):break
    witnesses=[]
    for coordinate in range(dimension):
        output=next((j for j,row in enumerate(rows) if row[coordinate]%p),None)
        if output is not None:
            witnesses.append({'coordinate':coordinate,'output_row':output,
                              'nonzero_multiplier':rows[output][coordinate],
                              'inverse_mod_p':pow(rows[output][coordinate]%p,-1,p)})
    result={
        'scope':'DERIVED/EXECUTED public algebra; no keys, encryptions, probes or attacks executed',
        'registry_sha256':hashlib.sha256(raw).hexdigest(),
        'field_p':p,'ambient_dimension':dimension,'original_projection_rank':rank,
        'diagonal_bilinear_probe_span_rank':len(witnesses),
        'reachable_coordinates':[w['coordinate'] for w in witnesses],
        'unreachable_coordinates':[i for i in range(dimension) if not any(w['coordinate']==i for w in witnesses)],
        'actual_semantic_input_last_coordinate':0,
        'number_of_feature_coordinates':576,
        'bilinear_formula':'Dec(C_u, Enc_v(e_i), SK_y_j) = y_j[i] * u[i]',
        'affine_bilinear_formula':'F_j(u,e_i)-F_j(u,0)-y_j[i] = gamma*y_j[i]*u[i]',
        'validity_condition':'Future writer can encode 0 and each e_i; gamma nonzero; exact bounded integer or field output',
        'basis_ciphertext_source':'AGT2022/1168 section5.2 p28: MCT1,i,j is a basis encryption already inside EK_i',
        'witnesses':witnesses,
        'runtime_crypto_calls':0,
    }
    (HERE/'INTERACTION_SPAN.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:result[k] for k in ['original_projection_rank','diagonal_bilinear_probe_span_rank','unreachable_coordinates','runtime_crypto_calls']}))

if __name__=='__main__':main()

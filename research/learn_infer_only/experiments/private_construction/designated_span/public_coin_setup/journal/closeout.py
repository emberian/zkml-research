#!/usr/bin/env python3
"""Summarize the completed report without opening private data or running crypto."""
from pathlib import Path
import argparse,csv,json
HERE=Path(__file__).resolve().parent

def main():
 p=argparse.ArgumentParser();p.add_argument('--reports',type=Path,required=True);a=p.parse_args();reports=a.reports.resolve()
 report=json.loads((reports/'report.json').read_bytes());public=json.loads((reports/'public_complete.json').read_bytes());assert report['ok']
 total=report['whole_public_phase_ns']/1e9;setup=public['setup']['setup_elapsed_ns']/1e9;replay=public['public_replay_ns']/1e9
 with (HERE/'COSTS.csv').open('w',newline='') as sink:
  writer=csv.DictWriter(sink,fieldnames=['label','role','command','count','seconds','source','scope']);writer.writeheader()
  writer.writerow({'label':'EXECUTED','role':'whole_public_phase','command':'normal40/4/8','count':1,'seconds':f'{total:.9f}','source':str(reports.relative_to(HERE))+'/public_complete.json:whole_public_phase_ns','scope':'setup,public operations,full replay,audits,exports,shutdown; private drain excluded'})
  writer.writerow({'label':'EXECUTED','role':'setup','command':'honest_public_setup_and_genesis','count':1,'seconds':f'{setup:.9f}','source':str(reports.relative_to(HERE))+'/public_complete.json:setup.setup_elapsed_ns','scope':'timer starts after params; includes registry,public construction/verification,finalization,queries,genesis/config'})
  writer.writerow({'label':'EXECUTED','role':'independent_public_replay','command':'all44transitions','count':44,'seconds':f'{replay:.9f}','source':str(reports.relative_to(HERE))+'/public_complete.json:public_replay_ns','scope':'full public ciphertext recomputation and state/history checks'})
  for row in public['role_command_costs']:writer.writerow({'label':'EXECUTED','role':row['role'],'command':row['command'],'count':row['count'],'seconds':f"{row['sum_ns']/1e9:.9f}",'source':str(reports.relative_to(HERE))+'/public_complete.json:role_command_costs','scope':'child process wall times; not additive with containing timers'})
 text=f'''# Public-coin setup and durable journal

[EXECUTED] The honest public-coin setup now joins the unchanged durable journal:
**40 Learn, four Infer, eight exact-original expiries and 44 finalized events**.
All 44 transitions pass full independent public arithmetic replay, and the
independent acceptor's complete ordered history equals the authority's history.
All four private signed integers match the independent fixture formula.
Orderly authority/acceptor reopening preserves revision 22; two exact authorized
historical retries preserve their signed envelopes and the final head. The second
private drain adds zero decodes. See [saved report]({reports.relative_to(HERE)}/report.json).

[EXECUTED phase order] Every public history operation, full replay, source/log/
storage check and service shutdown finishes before the first private drain.
[public_complete.json]({reports.relative_to(HERE)}/public_complete.json) is written
at that boundary. The public phase takes **{total:.9f} seconds**, including
**{replay:.9f} seconds** for the full independent replay. The setup timer records
{setup:.9f} seconds and starts after params; its exact scope and child costs are
in [COSTS.csv](COSTS.csv). Private answers, answer hashes and private durations
are omitted. Aggregate comparison publication is outside the host protocol.
These measurements are one normal run on a shared machine, not a speedup claim.

[DERIVED architecture; EXECUTED pins] [SOURCE_PINS.json](SOURCE_PINS.json) inventories
28 unchanged dependency copies: all eight journal/service modules, original four
crypto files (also copied beside setup), unchanged public setup adapter and
persistent host with its frozen source. The run pins 33 source/contract entries,
79 signature-library implementation files, interpreter and native OpenSSL library.
`setup_join.py` changes only setup orchestration. The new Run constructor consumes
the prepared genesis; normal issuance, authorization, acceptance and full replay
remain inherited. The host's inspection cache and full-byte blob hashing are
unchanged. [CONTRACT.md](CONTRACT.md) was frozen before launch.

[DERIVED / EXECUTED setup binding] Genesis binds the accepted public transcript,
registry, all 16 announcements, successful public-verification record, original
setup source, new join source and dependency inventory. Its digest is
`{report['genesis_sha256']}`; context identity is
`{report['context_id']}`. Existing canonical genesis binding propagates this
extension into each signed action, state, transition and installed head. The
unchanged services pin that complete genesis; they do not newly prove an honest
sampler or re-execute public setup. The trusted initializer fully verifies the
public completion equations and existing context algebra before continuation.

[EXECUTED credential path; DERIVED limits] The actual commands create independent
registration-signing keys, recipient-owned scalars, public tau/U construction,
full public verification and recipient finalization. No keygen, initializer or
recipient-register command executes; the scalar master and private projection
deliveries are absent from this setup path. The frozen backend still contains
those unused legacy commands. Registration authentication keys and all 16 dedicated
recipient scalars survive; redundant pending copies are removed without a
physical-erasure claim. The acceptance service has no recipient scalar path.

[DERIVED scope] Honest direct tau/U sampling and honest independent fixed-slot
registration remain premises. Each recipient holds its full per-input fixed
query credential; their coalition exposes the whole fixed span on all retained
ciphertexts, including expired inputs. Journal dedup is software behavior and
does not cryptographically restrict that coalition. Inputs use the preregistered
known formula `((n+3)*(j+5) mod 17)-8`, with zero initial state and fresh OS-backed
encryption randomness. This is arithmetic integration, not model utility or a
private learned lifetime. Shared-account processes provide no OS isolation or
operator confidentiality. Classical DDH, Ed25519 and SHA-256 remain separate
assumptions; no malicious-setup, selected-only release, nonlinear-learning,
hardware-finality or post-quantum result is claimed.


[DERIVED timing boundary] Genesis commits the complete setup verification and
context-validation records, including their public process-work timing metadata.
The emitted research logs also measure role durations. The reviewed DDH argument
for accepted tau/U/A values is therefore not a theorem for this whole instrumented
journal view. Physical timing and correlated environment observations remain
outside that theorem, including when committed into genesis. No stronger
confidentiality claim is inferred from this normal functional run.

[EXECUTED retained failure] The first wrapper launch stopped before registration
because it precreated the directory that unchanged auth-init must create itself.
Only params succeeded; no keys, public sampling, services or events were
produced. [normal_001/ATTEMPT.md](reports/normal_001/ATTEMPT.md), exact output and
all 33 source snapshot entries preserve that attempt. The corrected wrapper
removes only premature registration-directory creation. No frozen dependency
or original adapter workload was modified or rerun.

[EXECUTED reproduction/provenance] Exact launch argv and stdout/stderr are retained
in [{reports.name}/COMMAND.json]({reports.relative_to(HERE)}/COMMAND.json).
`seal.py` checks saved signatures, complete ordered parent/FIFO identities and
source origins without DDH execution, RPC or private-file reads; private score
success remains attributed to the pinned executed report. `FINAL_MANIFEST.json`
pins public code and evidence, including the preserved failed attempt. Earlier
adapter closeout lives in [../adapter/CLOSEOUT.md](../adapter/CLOSEOUT.md).

```sh
python3 driver.py prepare --reports reports/FRESH_NAME
python3 driver.py run --root runtime/FRESH_NAME --reports reports/FRESH_NAME
python3 closeout.py --reports {reports.relative_to(HERE)}
python3 seal.py --reports {reports.relative_to(HERE)}
```

[DERIVED review boundary] Independent review has a separate parent-owned
disposition. No rerun is needed to seal this completed normal workload; no
full384/96 run is authorized by these example commands.

[OPEN next] A stronger recipient-release restriction and honest sampler
enforcement remain separate construction obligations. Root owns shared
STATUS/NEXT and commits. This lane used no network/metered queries or companion
edits and no adversarial, routing, extraction or malformed-input experiment.
'''
 (HERE/'README.md').write_text(text)
 print(json.dumps({'ok':True,'whole_public_seconds':total,'public_replay_seconds':replay,'outputs':['README.md','COSTS.csv'],'private_files_read':0}))
if __name__=='__main__':main()

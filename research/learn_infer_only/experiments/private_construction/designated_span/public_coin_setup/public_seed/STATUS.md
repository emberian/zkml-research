# Public seed setup lane

[DERIVED, 2026-09-08] Complete candidate theorem in PROPOSAL.md: recipient
registry first, then malicious polynomial seed search; hash accepted field
elements and square the free-coordinate values. The proof programs a guessed
seed's complete oracle transcript using public square roots and the existing
IPFE-to-designated view simulator. Independent review remains pending.

[DERIVED] A fixed-cap bit rejection sampler has the proposed exact finite-tape
simulator, including failed candidates. The stated bound is
`Delta≤2*M*N*epsilon_DDH+2*min(1,Q_pre/q^m)`, with all resources included:
M is the existing message/kernel padding; N pads the number of first-touched
seed candidates through selection. The latter is at most Q_post+1. Public
cap failure is exactly simulated and contributes no additive privacy term;
the separate bounded scalar-sampler correction is written explicitly.

[EXECUTED] finite_witness.py exits zero. Its 55,296 public F7 simulator
choices map to all 3,072 registry/tape transcripts uniformly, including
failed candidates. Accepted-value coupling, group completion, a nontrivial
kernel pair and two false shortcuts are checked. All numbers and command
output are retained in finite_witness.log and SOURCES.md.

[EXECUTED scope] Only this directory is owned. Prior setup, reviews, journal,
shared ledgers and companion trees are frozen. No crypto runtime, private
artifact, extraction task or stopped routing task has been used.

[EXECUTED source counts] Two web search queries; two primary page opens;
two RFC page finds;
zero Scry SQL/schema calls, zero Kagi calls, zero eprint HTTP/PDF requests.
One existing local primary PDF read: ePrint 2009/340. Exact access levels and
counts are finalized in SOURCES.md. No novelty or literature-wide absence claim.

[OPEN] Root was sent the proof draft and requested to assign independent
review. NEXT.md gives the four load-bearing review obligations. Concrete
hashes, QROM, malicious registration, multiple challenge setups and physical
timing remain outside the theorem. There is no honest-beacon premise and no
hidden setup credential in the prescribed public algorithm.

/- Public fixture export only. No new theorem or cryptographic checker. -/
import Assurance.ResidentDurableIntegration
open Lean
open Minidregg.Assurance.ResidentDurableIntegration
open Minidregg.Assurance.ResidentReleaseContext
open Minidregg.Kernel.DurableDataIntent
open Minidregg.Theory.ResourceCost
namespace PersistentFixture

def bytes (bs : List UInt8) : Json := toJson (bs.map UInt8.toNat)
def eventJson (e : StableEvent) : Json := Json.mkObj [
  ("codec_version",toJson e.codecVersion),("domain",toJson e.domain.value),
  ("event_id",toJson e.eventId.value),("canonical_bytes",bytes e.canonicalBytes)]
def tokenJson (e : StableNullifier) : Json := Json.mkObj [
  ("codec_version",toJson e.codecVersion),("domain",toJson e.domain.value),
  ("nullifier_id",toJson e.nullifierId.value),("canonical_bytes",bytes e.canonicalBytes)]
def contextJson (c : Context) : Json := Json.mkObj [
  ("genesis",toJson c.genesis),("parent",toJson c.parent),("program",toJson c.program),
  ("version",toJson c.version),("command",toJson c.command),
  ("authorization",toJson c.authorization),("recipient",toJson c.recipient),
  ("randomness_rule",toJson c.randomnessRule),("randomness_commitment",toJson c.randomnessCommitment),
  ("next",toJson c.next),("output",toJson c.output)]
def lanes : List (String × Lane) := [("incidences",.incidences),("turnBytes",.turnBytes),
  ("memoryTouches",.memoryTouches),("witnessBytes",.witnessBytes),("proofWork",.proofWork),
  ("storageBytes",.storageBytes),("networkBytes",.networkBytes),("sideEffectCount",.sideEffectCount),
  ("feeDebit",.feeDebit),("leaseByteBlocks",.leaseByteBlocks)]
def planJson (p : Plan Minidregg.Theory.CellStateWitness.materializer) : Json := Json.mkObj [
  ("context",contextJson p.context),
  ("openings",Json.mkObj [("genesis_id",toJson p.genesisId.value),("state_id",toJson p.stateId.value),
    ("genesis_bytes",bytes p.genesis.bytes),("pre_bytes",bytes p.pre.bytes),
    ("prior",toJson ([] : List Nat)),("epoch",toJson p.epoch)]),
  ("intent",Json.mkObj [("transaction_id",toJson p.transactionId.value),
    ("writes",toJson (p.intent.writes.map fun w=>Json.mkObj [("cell_id",toJson w.cellId.value),
      ("expected_pre",toJson w.expectedPre.value),("exact_post",toJson w.exactPost.value),
      ("canonical_post_bytes",bytes w.canonicalPostBytes)])),
    ("read_guards",toJson (p.intent.readGuards.map fun g=>Json.mkObj [
      ("cell_id",toJson g.cellId.value),("expected_root",toJson g.expectedRoot.value)])),
    ("nullifiers",toJson (p.intent.nullifiers.map tokenJson)),
    ("exact_charge",Json.mkObj (lanes.map fun (name,lane)=>(name,toJson (p.intent.exactCharge lane)))),
    ("event",eventJson p.packet)])]

def fixture : Json := Json.mkObj [
  ("schema_version",toJson (1 : Nat)),
  ("scope",toJson "Public accepted Bool context/intent fixture; computational gate is an explicit fixture premise, not cryptographic verification."),
  ("accepted_subject",toJson "Minidregg.Assurance.ResidentDurableIntegration.Closed.subject"),
  ("primary",planJson Closed.p),("racing",planJson Closed.racing),
  ("selected",Json.mkObj [("genesis_id",toJson Closed.selected.genesisId.value),
    ("state_id",toJson Closed.selected.stateId.value),("genesis_bytes",bytes Closed.selected.genesisBytes),
    ("authorization",toJson Closed.selected.authorization),("recipient",toJson Closed.selected.recipient)]),
  ("initial",Json.mkObj [("state_bytes",bytes Closed.p.pre.bytes),("state_root",toJson Closed.p.pre.root.value),
    ("budget",Json.mkObj (lanes.map fun (name,lane)=>(name,toJson (Closed.before.model.available lane))))]),
  ("checked",Json.mkObj [("primary_preflight",toJson (decide (Closed.p.intent.preflight Closed.before=.ok ()))),
    ("primary_openings",toJson (Closed.p.opens Closed.selected Closed.before)),
    ("primary_finality",toJson (Minidregg.Kernel.FinalityGate.check Closed.q Closed.book Closed.p.candidate Closed.cert)),
    ("racing_preflight_at_initial",toJson (decide (Closed.racing.intent.preflight Closed.before=.ok ())))])]
#eval IO.println fixture.compress
end PersistentFixture

/- Scope tooth: the reviewed ExecutedHistory consists exclusively of window
admissions. An ordinary extra journal transaction is outside that carrier. -/
import Assurance.CiphertextWindowWitness

namespace WindowJournalFrameWitness
open Minidregg.Assurance.CiphertextWindowWitness
open Minidregg.Assurance.CiphertextWindowCell
open Minidregg.Kernel.DurableDataIntent
set_option autoImplicit false

def journalOnly : DataIntent hash where
  transactionId:=⟨404⟩
  writes:=[⟨⟨23⟩,⟨0⟩,⟨0⟩,data3.canonicalBytes ⟨23⟩⟩]
  readGuards:=[]
  nullifiers:=[]
  exactCharge:=0
  event:=⟨0,⟨0⟩,⟨404⟩,[]⟩
  postRootsBound:=by
    intro write h
    simp only [List.mem_singleton] at h
    subst write
    rfl
  guardsReadOnly:=by intro guard h;cases h

def afterJournal := DataSnapshot.install data3 journalOnly

theorem unrelated_journal_transaction_is_outside_window_history :
    execute .complete data3 journalOnly=.accepted afterJournal ∧
    afterJournal.canonicalBytes selected.stateId=(stateStream ct).encode s3 ∧
    afterJournal.model.journal.length=4 ∧
    ¬ExecutedHistory ct hash admit 2 selected data0 afterJournal s3 := by
  have ready : journalOnly.preflight data3=.ok () := by decide +kernel
  have fresh : Minidregg.Kernel.DurableCommitProtocol.Snapshot.lookupRecorded
      journalOnly.transactionId data3.model.journal=none := by decide +kernel
  refine ⟨execute_complete_ready data3 journalOnly fresh ready,?_,rfl,?_⟩
  · exact executed_history_subject.1
  · intro h
    have count := (executed_history_invariant ct hash admit 2 selected data0 afterJournal s3 h).2.1
    change 3=4 at count
    contradiction

/-- info: 'WindowJournalFrameWitness.unrelated_journal_transaction_is_outside_window_history' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms WindowJournalFrameWitness.unrelated_journal_transaction_is_outside_window_history

end WindowJournalFrameWitness

import PoissonPTX.CellEntryRebase
import PoissonPTX.CellEntryProducerChecks
import PoissonPTX.SourceCheck
import PoissonPTX.TailExecute

namespace PtxTorchLean.Poisson.PTX.CellEntry.RebaseChecks
open Ptx Checks
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

/-- Continue the real nonzero entry state; do not install shared input bytes. -/
def bodyStart := continuation result.state
def bodyContext (u : Fin 32) : Kernel.Context := ⟨4096,BitVec.ofNat 32 u.val,1⟩
def choose (_ : Fin 32) (pc : Nat) : Word :=
  if pc=7 then read64 memory 4112 else 0xc000000000000000

/-- Lane two loads the first coefficient and then lane zero's gathered word. -/
def candidate := Concurrent.WithTail.execute cfg bodyContext (Concurrent.CellConsumer.WithOutput.front 2)
  (CellFinal.tail 2 256) choose (List.replicate 13 (2 : Fin 32)) bodyStart

def bodyResult : Concurrent.WithTail.Outcome 32 := candidate.getD ⟨bodyStart,[]⟩

theorem executed : candidate=some bodyResult := by
  have yes : candidate.isSome=true := by decide +kernel
  cases h : candidate with
  | none => simp [h] at yes
  | some out => simp [bodyResult,h]

theorem actual_body : Concurrent.WithTail.Runs cfg bodyContext (Concurrent.CellConsumer.WithOutput.front 2)
    (CellFinal.tail 2 256) bodyStart bodyResult.events bodyResult.state := Concurrent.WithTail.execute_sound executed

theorem reads : bodyResult.events=[
    .data 2 ⟨.global,⟨7,false,4112,0x100000003⟩⟩,
    .data 2 ⟨.shared,⟨12,false,256,0xc000000000000000⟩⟩] := by decide +kernel

def whole := result.events++bodyResult.events
def sources (r : Nat) (k : Fin 8) : Sources.Origin Nat := if r=42 then .store 1 k else .initial

attribute [local irreducible] result bodyResult whole

theorem checked : Concurrent.SourceCheck.Checked initial whole sources := by decide +kernel

theorem compatible : Concurrent.Visibility.Compatible initial whole sources := Concurrent.SourceCheck.sound (initial:=initial) (events:=whole) (source:=sources) checked

/-- Only the final observation is a shared read, and it chooses the actual
prefix store for every byte. This is a necessary-source certificate. -/
theorem shared_read_at {r : Nat} {reader : Fin 32} {access : Concurrent.Access} (observed : whole[r]?=some (.data reader access))
    (read : access.data.store=false) (shared : access.space=.shared) : r=42 := by
  let check (index : Fin whole.length) : Bool := match whole[index.val] with
    | .data _ a => if !a.data.store && a.space==.shared then index.val==42 else true
    | .barrier _ => true
  have positions : ∀ index, check index=true := by decide +kernel
  obtain ⟨bound,atIndex⟩ := List.getElem?_eq_some_iff.mp observed
  have here := positions ⟨r,bound⟩
  simpa only [check,atIndex,read,shared,Bool.not_false,Bool.true_and,beq_self_eq_true,
    ite_true,beq_iff_eq] using here

theorem performed : Concurrent.Visibility.Performed whole sources := by
  intro w r writer reader wa ra hw hr write read sw sr across j k address
  have atRead := shared_read_at hr read sr
  simp [sources,atRead]

theorem snapshot_sound : Concurrent.SourceCut.Published initial (publication 2 (by decide) bases initial result.state)
    result.events := publication_sound actual_run ProducerChecks.aligned (by intro u; rfl)
      Checks.compatible index_compatible (by intro u; rfl) completed.1 (by decide) (by decide)
      (by decide) ProducerChecks.valid (by decide)

/-- Actual body reads admit the derived snapshot view while the executed
lane memory still contains its own, separately gathered slot. -/
theorem rebased_sources :
    Concurrent.Visibility.Compatible (publication 2 (by decide) bases initial result.state)
      bodyResult.events (Concurrent.SourceCut.source result.events.length sources) ∧
    Concurrent.Visibility.Performed bodyResult.events (Concurrent.SourceCut.source result.events.length sources) :=
  body_sources actual_run ProducerChecks.aligned (by intro u; rfl) Checks.compatible index_compatible
    (by intro u; rfl) completed.1 (by decide) (by decide) (by decide) ProducerChecks.valid
    (by decide) (by decide) (by decide) actual_body (by rfl)
    (by simpa only [whole] using compatible) (by simpa only [whole] using performed)

theorem cross_lane_read : (bodyResult.state.core.lanes 2).regs 5=0xc000000000000000 ∧
    read64 (bodyStart.core.lanes 2).shared 256=0x5a5a5a5a5a5a5a5a ∧
    read64 (publication 2 (by decide) bases initial result.state .shared) 256=0xc000000000000000 := by decide +kernel

end PtxTorchLean.Poisson.PTX.CellEntry.RebaseChecks

import PoissonPTX.CellTailProgram
import PoissonPTX.TailExecute
import PoissonPTX.CellMiddleWitness

namespace PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.WithOutput.Checks
open Ptx WithTail CellMiddle
set_option maxRecDepth 100000
set_option maxHeartbeats 40000000

/-- The existing Q1 zero-data arena, extended by four output words. -/
def start : WithTail.State 32 :=
  ⟨⟨fun t => {Witness.seed t with globalBytes:=192},Barrier.reset 0,none⟩,
    fun _ => false,fun _ => false⟩

def ctx (t : Fin 32) : Kernel.Context := ⟨0,BitVec.ofNat 32 t.val,0⟩

/-- Lane zero stores and returns before lane one starts final arithmetic.
Padding lanes execute the real return without an output store. -/
def schedule : List (Fin 32) := Witness.schedule++(List.finRange 32).flatMap fun t =>
  List.replicate (if t.val<4 then (body 2).length+7 else 2) t

def candidate : Option (WithTail.Outcome 32) :=
  WithTail.execute Witness.cfg ctx (front 2) (CellFinal.tail 2 160) (fun _ _ => 0) schedule start

theorem successful : candidate.isSome=true := by decide +kernel

def result : WithTail.Outcome 32 := candidate.getD ⟨start,[]⟩

theorem executed : candidate=some result := by
  have h := successful
  cases he : candidate with
  | none => simp [he] at h
  | some out => simp [result,he]

attribute [local irreducible] result

theorem actual_run :
    WithTail.Runs Witness.cfg ctx (front 2) (CellFinal.tail 2 160) start result.events result.state :=
  WithTail.execute_sound executed

theorem returned : ∀ t, result.state.halted t=true ∧
    (result.state.core.lanes t).pc=(front 2).length+6 := by decide +kernel

theorem padding_did_not_store : ∀ t : Fin 32, 4≤t.val →
    (result.events.filter fun e => match e with
      | .data thread a => thread==t && a.space==.global && a.data.store
      | _ => false).length=0 := by decide +kernel

theorem four_outputs :
    (result.events.filter fun e => match e with
      | .data _ a => a.space==.global && a.data.store
      | _ => false).length=4 := by decide +kernel

/-- A concrete output store precedes a different lane's remaining global read. -/
theorem interleaved :
    (result.events.dropWhile fun e => match e with
      | .data _ a => !(a.space==.global && a.data.store)
      | _ => true).any (fun e => match e with
      | .data t a => t==1 && a.space==.global && !a.data.store
      | _ => false)=true := by decide +kernel

theorem stopped_again :
    WithTail.tick Witness.cfg ctx (front 2) (CellFinal.tail 2 160) (fun _ _ => 0) 0 result.state=none := by
  simp [WithTail.tick,(returned 0).1]

theorem projected :
    ∃ small shadow, Concurrent.Runs Witness.cfg (program 2) start.core small shadow ∧
      Nonempty (Projection.Embedding small result.events) ∧
      WithTail.Related (program 2).length 11 result.state.core shadow :=
  arithmetic (by decide) (by decide) actual_run
    (by intro t h; simp [start,Barrier.reset] at h) (by intro t; rfl)

end PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.WithOutput.Checks

import PoissonPTX.CellMiddle
namespace PtxTorchLean.Poisson.PTX.Concurrent.CellMiddle.Witness
open Ptx
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

def seed (t : Fin 32) : PTX.State := {
 pc:=0, regs:=fun r => if r=14 then BitVec.ofNat 64 t.val else
   if r=16 then BitVec.ofNat 64 (t.val/2) else if r=17 then BitVec.ofNat 64 (t.val%2) else 0,
 global:=fun _ => 0,shared:=fun _ => 0,globalStart:=0,globalBytes:=160,sharedStart:=0,sharedBytes:=224 }
def start : State 32 := ⟨seed,Barrier.reset 0,none⟩
def cfg : Config 32 := ⟨0,by decide⟩
def schedule : List (Fin 32) :=
  [first 2 0 64, second 2 0 64 128, third 2 0 64].flatMap fun body =>
    (List.finRange 32).flatMap (fun t => List.replicate (if t.val<4 then body.length+1 else 1) t) ++ List.finRange 32
def candidate : Option (Outcome 32) :=
  execute cfg (code 2 0 64 128) (fun _ _ => 0) schedule start

theorem successful : candidate.isSome=true := by decide +kernel

/-- This schedule includes all 32 barrier participants, with 28 padding lanes. -/
def result : Outcome 32 :=
  candidate.getD ⟨start,[]⟩

theorem executed : candidate=some result := by
  have h := successful
  cases he : candidate with
  | none => simp [he] at h
  | some out => simp [result,he]

theorem candidate_run : Runs cfg (code 2 0 64 128) start result.events result.state :=
  execute_sound executed

theorem finished : result.state.barrier.generation=3 ∧
    ∀ t, (result.state.lanes t).pc=(code 2 0 64 128).length := by decide +kernel

end PtxTorchLean.Poisson.PTX.Concurrent.CellMiddle.Witness

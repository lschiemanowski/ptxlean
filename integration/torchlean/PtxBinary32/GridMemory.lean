import PtxBinary32.GridExecution
import Ptx.TraceMemory

/-! The actual last global store determines each final global word, independently
of candidate load values. Storage identities separate each group's scratch. -/
namespace Ptx.Scalar.Parallel.Grid
open Ptx.TraceMemory (Location)

def location (g : Fin groups) (space : Space) (address : Scalar.Address) : Location (groups+1) :=
  ⟨match space with | .global => 0 | .shared => ⟨g.val+1,by omega⟩,address.toNat/4⟩

theorem shared_private (g h : Fin groups) (a b : Scalar.Address) (different : g≠h) :
    (location g .shared a).code≠(location h .shared b).code := by
  intro eq
  have slots := congrArg (fun l : Location (groups+1) => l.storage.val) (Location.code_injective eq)
  apply different; apply Fin.ext
  simpa [location] using slots

theorem global_shared_distinct (g h : Fin groups) (a b : Scalar.Address) :
    (location g .global a).code≠(location h .shared b).code := by
  intro eq
  have slots := congrArg (fun l : Location (groups+1) => l.storage.val) (Location.code_injective eq)
  simp [location] at slots

theorem global_common (g h : Fin groups) (a : Scalar.Address) : location g .global a=location h .global a := rfl

def latestGlobal (index : Nat) (events : List (Event groups n)) : Option Word :=
  Replay.latestWrite .global index (events.map Prod.snd)

theorem latestGlobal_append (index : Nat) (left right : List (Event groups n)) :
    latestGlobal index (left++right)=(latestGlobal index right).or (latestGlobal index left) := by
  simp [latestGlobal,Replay.latestWrite_append]

theorem step_global_value (step : Step cfg program s events final) (index : Nat) :
    final.global[index]?=(latestGlobal index events).or s.global[index]? := by
  cases step with
  | issue g t candidate out step =>
    have value := Replay.run_value (Parallel.Runs.cons step Parallel.Runs.nil) .global index
    simpa [latestGlobal,tag,List.map_map,Function.comp_def,Replay.arena,Replay.arrays,install,view] using value

theorem run_global_value (run : Runs cfg program s events final) (index : Nat) :
    final.global[index]?=(latestGlobal index events).or s.global[index]? := by
  induction run with
  | nil => rfl
  | cons step _ ih => rw [ih,step_global_value step,latestGlobal_append,Option.or_assoc]

theorem unchanged_global (run : Runs cfg program s events final) (index : Nat)
    (unwritten : latestGlobal index events=none) : final.global[index]?=s.global[index]? := by
  rw [run_global_value run,unwritten]; rfl

/-- A writable region must be justified from actual emitted events. This theorem
only consumes an explicit no-write proof; it does not assume kernel ownership. -/
theorem global_frame (run : Runs cfg program s events final) (preserve : Nat → Prop)
    (unwritten : ∀ i, preserve i → latestGlobal i events=none) :
    ∀ i, preserve i → final.global[i]?=s.global[i]? := fun i hi => unchanged_global run i (unwritten i hi)

end Ptx.Scalar.Parallel.Grid

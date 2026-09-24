import Ptx.SharedReductionProgram
import Ptx.SharedReductionMemoryUniversal
import Ptx.SharedReductionSafety

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace Ptx.Scalar.SharedReduction.Examples

open Machine

private def seed : Seed := ⟨fun _ => 0x12345678, fun _ => 0xffff, fun _ => true⟩
private def cfg2 : Config 2 := ⟨by decide,by decide,7⟩
private def cfg32 : Config 32 := ⟨by decide,by decide,7⟩
private def cfg64 : Config 64 := ⟨by decide,by decide,7⟩

set_option maxRecDepth 100000 in
example : (Machine.run cfg2 (fullSchedule cfg2)
    (start [0xffffffff,2,77,88] [91,92,93] (fun _ => seed))).state.global =
      [0xffffffff,2,1,88] := by decide

set_option maxRecDepth 100000 in
example : (Machine.run cfg2 (fullSchedule cfg2)
    (start [3,5,77] [91,92,93] (fun _ => seed))).state.shared = [3,5,93] := by decide

private def input32 : List Word := (List.range 32).map (BitVec.ofNat 32) ++ [999,777]
private def input64 : List Word := (List.range 64).map (BitVec.ofNat 32) ++ [999,777]

-- These instantiate the all-input theorem, including two full warps at 64 lanes.
-- They do not assume a warp execution model or constitute hardware tests.
example : (Machine.run cfg32 (fullSchedule cfg32)
    (start input32 (List.replicate 35 123) (fun _ => seed))).state.global =
      (List.range 32).map (BitVec.ofNat 32) ++ [496,777] := by
  have result := (full_execution cfg32 input32 (List.replicate 35 123) (fun _ => seed)
    (by decide) (by decide)).1
  exact result.trans (by decide)

example : (Machine.run cfg64 (fullSchedule cfg64)
    (start input64 (List.replicate 65 123) (fun _ => seed))).state.global =
      (List.range 64).map (BitVec.ofNat 32) ++ [2016,777] := by
  have result := (full_execution cfg64 input64 (List.replicate 65 123) (fun _ => seed)
    (by decide) (by decide)).1
  exact result.trans (by decide)

-- One missing participant leaves the barrier incomplete; repeated dispatch of
-- the waiting lane cannot fabricate the other arrival or complete the phase.
private def incompleteSchedule : List (Fin 2) :=
  producerSchedule (List.finRange 2) ++ [0,0,0]
set_option maxRecDepth 100000 in
example : (Machine.run cfg2 incompleteSchedule
    (start [3,5,77] [91,92] (fun _ => seed))).state.barrier.generation = 0 := by decide
set_option maxRecDepth 100000 in
example : (Machine.run cfg2 incompleteSchedule
    (start [3,5,77] [91,92] (fun _ => seed))).state.global = [3,5,77] := by decide

-- An oracle can propose a wrong load value, but source compatibility rejects it.
private def badStart : Machine.State 2 := start [3,5,77] [91,92] (fun _ => seed)
private def badReads : Nat → Option Word := fun _ => some 99
private def badSchedule : List (Fin 2) := List.replicate 4 0
private def badRead : Fin (Memory.runLabels cfg2 badReads badSchedule badStart).length := ⟨5,by decide⟩
example (source co) : ¬(Memory.runGraph cfg2 badReads badSchedule badStart source co).Sources := by
  intro sources
  have forced := Memory.run_global_input_read cfg2 badReads badSchedule badStart source co badRead
    sources (by change True; trivial) 0 (by decide) (by rfl)
  have impossible : (99 : Word) = 3 := forced.2.2
  contradiction

-- The candidate interpreter can propose a stale shared observation after the
-- real barrier. Memory admission, rather than a forced read in the interpreter,
-- rejects this incorrect completed candidate.
private def staleReads : Nat → Option Word := fun i => if i = 27 then some 91 else none
private def staleExecution := Machine.runWith cfg2 staleReads (fullSchedule cfg2) badStart
private def staleOccurrence : Scalar.Occurrence :=
  match staleExecution.trace[28]? with
  | some (Machine.Event.scalar _ _ _ occurrence) => occurrence
  | _ => Scalar.occurrence (badStart.lanes 0).scalar (.plain (.mov32 0 (.imm 0))) false

example : staleExecution.state.global = [3,5,96] := by decide
example : ∀ thread, (staleExecution.state.lanes thread).halted = true := by decide
private theorem stale_at : staleExecution.trace[28]? =
    some (Machine.Event.scalar (0 : Fin 2) .loop (some .shared) staleOccurrence) := by decide
private theorem stale_memory : staleOccurrence.memory =
    some (⟨.load,(0 : Address),(91 : Word)⟩ : MemoryEffect) := by decide

example (source co) :
    ¬Graph.Ordered.Valid
      (Memory.runGraph cfg2 staleReads (fullSchedule cfg2) badStart source co)
      (Memory.extra [3,5,77] [91,92] staleExecution.trace source co) := by
  intro valid
  have forced := Memory.run_shared_load_value cfg2 staleReads (fullSchedule cfg2)
    [3,5,77] [91,92] (fun _ => seed) 28 (0 : Fin 2) Machine.Block.loop staleOccurrence
    (⟨.load,(0 : Address),(91 : Word)⟩ : MemoryEffect) stale_at stale_memory rfl
    0 (by decide) rfl source co valid
  have impossible : (91 : Word) = 3 := forced.2
  contradiction

end Ptx.Scalar.SharedReduction.Examples

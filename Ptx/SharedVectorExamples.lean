import Ptx.SharedVector
import Ptx.ScalarRules

/-! Kernel-checked examples exercising real shared-allocation interleavings and
reusable segment composition. Initial register values below are explicit inputs. -/
namespace Ptx.Scalar.SharedVector.Examples

def memory : List Word := [7,9,100,4294967295,2,200,99]
def registers : Fin 2 → Nat → Word := fun _ _ => 0

/-- Both lanes run in one allocation; the second sum wraps, and the tail is untouched. -/
theorem round_robin_result :
    (execute (schedule 2) (initial memory registers)).memory =
      [7,9,16,4294967295,2,1,99] := by decide

/-- The same result under a different instruction ordering, not atomic whole-lane calls. -/
def uneven : List (Fin 2) := [0,0,1,0,1,1,1,0,1,0]

theorem uneven_result :
    (execute uneven (initial memory registers)).memory = [7,9,16,4294967295,2,1,99] ∧
    Complete (execute uneven (initial memory registers)) := by unfold Complete; decide

/-- Repeatedly scheduling only one lane does not finish the other one. -/
theorem unfair_schedule_incomplete :
    ¬Complete (execute (List.replicate 20 (0 : Fin 2)) (initial memory registers)) := by unfold Complete; decide

/-- Five dispatches per lane construct an actual instruction-level execution. -/
theorem concrete_execution_exists :
    ∃ final : State 2, Execution (schedule 2) (initial memory registers) final ∧ Complete final := by
  exact ⟨_,execute_faithful memory _ _ (by decide) (by decide) (initial_invariant ..),
    schedule_complete memory registers⟩

/-- The mathematical transition is not used as proof of instruction execution
when its allocation contract fails: the actual scalar instruction faults. -/
theorem empty_arena_not_faithful :
    ¬FaithfulStep (initial [] (fun (_ : Fin 1) _ => 0)) 0 := by
  simp [FaithfulStep,initial,view,program,left,pointer,step,stepWith,eval,
    Guard.eval,Instr.plain,Operand64.eval,addressIndex]

end Ptx.Scalar.SharedVector.Examples

namespace Ptx.Scalar.Rules.Examples

def setThenExit : List Instr := [.plain (.mov32 0 (.imm 7)),.plain .exit]

theorem set_segment : Segment setThenExit 1 (fun s => s.pc = 0)
    (fun s => s.pc = 1 ∧ s.regs 0 = 7) := by
  intro s h
  simp [run,runWith,stepWith,setThenExit,eval,Instr.plain,Guard.eval,Operand32.eval,h,update]

theorem exit_segment : Completed setThenExit 1 (fun s => s.pc = 1 ∧ s.regs 0 = 7)
    (fun s => s.regs 0 = 7) := by
  intro s h
  simp [run,runWith,stepWith,setThenExit,eval,Instr.plain,Guard.eval,h.1,h.2]

/-- A completed contract assembled from independently checked execution segments. -/
theorem composed_completion : Completed setThenExit 2 (fun s => s.pc = 0)
    (fun s => s.regs 0 = 7) := segment_then_completed set_segment exit_segment

/-- The generic frame rule preserves any existing or absent memory index. -/
theorem composed_frame (s : Scalar.State) (pc : s.pc = 0) (index : Nat) :
    (run 2 setThenExit s).state.memory[index]? = s.memory[index]? := by
  apply run_frame
  simp [TraceAvoids,StoresTo,run,runWith,stepWith,setThenExit,eval,Instr.plain,
    Guard.eval,Operand32.eval,pc,occurrence]

end Ptx.Scalar.Rules.Examples

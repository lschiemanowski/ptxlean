import Ptx.SharedReductionResult

namespace Ptx.Scalar.SharedReduction.Machine.Writeback

/-- Persistent global memory is unchanged until output, then contains the exact
writeback. Reaching output PC1 records that the store actually succeeded. -/
def Invariant (input : List Word) (s : State n) : Prop :=
  (s.global = input ∨ s.global = input.set n (total input n)) ∧
  ∀ thread, (s.lanes thread).block = .output → (s.lanes thread).scalar.pc = 1 →
    s.global = input.set n (total input n)

theorem initial (input scratch : List Word) (seeds : Fin n → Seed) :
    Invariant input (start input scratch seeds) := by
  refine ⟨.inl rfl,?_⟩
  intro thread block
  contradiction

set_option maxHeartbeats 800000 in
private theorem selected_step (cfg : Config n) (reads : Option Word) (s : State n)
    (thread : Fin n) (input : List Word) (extent : n < input.length)
    (sum : ResultProof.LaneInvariant n input (s.lanes thread)) (before : Invariant input s) :
    ((step cfg reads thread s).state.global = s.global ∨
      (step cfg reads thread s).state.global = input.set n (total input n)) ∧
    (((step cfg reads thread s).state.lanes thread).block = .output →
    ((step cfg reads thread s).state.lanes thread).scalar.pc = 1 →
      (step cfg reads thread s).state.global = input.set n (total input n)) := by
  have length : s.global.length = input.length := by
    rcases before.1 with h | h <;> simp [h]
  have noWrap : 4*n < 2^64 := by have := cfg.noWrap; omega
  have address : addressIndex s.global (bytePointer n) = .ok n := by
    simp [addressIndex,bytePointer,Nat.mod_eq_of_lt noWrap,length,extent]
  have written := before.2 thread
  have memory := before.1
  by_cases stopped : (s.lanes thread).halted = true
  · simp only [step,stopped,↓reduceIte]
    exact ⟨Or.inl trivial,written⟩
  have alive : (s.lanes thread).halted = false := Bool.eq_false_iff.mpr stopped
  cases hb : (s.lanes thread).block
  all_goals rcases hp : (s.lanes thread).scalar.pc with _ | _ | _ | _ | _ | _ | _ | _ | k
  all_goals cases pred : (s.lanes thread).scalar.preds 0
  all_goals simp only [ResultProof.LaneInvariant,hb,hp] at sum
  all_goals simp [step,alive,hb,hp,program,dispatch,scalarStep,eval,Instr.plain,Guard.eval,
    Operand32.eval,Operand64.eval,setLane,sharedStore,pred,address]
  all_goals try {
    cases disposition : (Barrier.step (barrierConfig cfg) s.barrier
      (barrierRequest cfg s thread 0)).disposition <;> simp_all }
  all_goals cases sa : addressIndex s.shared ((s.lanes thread).scalar.addrs 0)
  all_goals cases ga : addressIndex s.global ((s.lanes thread).scalar.addrs 0)
  all_goals try simp_all
  all_goals rcases memory with hm | hm <;> simp_all [List.set_set]

theorem step_preserves (cfg : Config n) (reads : Option Word) (s : State n)
    (thread : Fin n) (input : List Word) (extent : n < input.length)
    (sum : ResultProof.Invariant n input s) (before : Invariant input s) :
    Invariant input (step cfg reads thread s).state := by
  obtain ⟨memory,selected⟩ := selected_step cfg reads s thread input extent (sum thread) before
  constructor
  · rcases memory with same | written
    · rw [same]; exact before.1
    · exact .inr written
  · intro other block pc
    by_cases same : other = thread
    · subst other; exact selected block pc
    · by_cases released : (step cfg reads thread s).status = .released
      · rw [Data.release_lane_fields cfg reads s thread other released] at block
        contradiction
      · rw [Data.step_other cfg reads s thread other same released] at block pc
        rcases memory with unchanged | written
        · exact unchanged.trans (before.2 other block pc)
        · exact written

theorem runWith_preserves (cfg : Config n) (reads : Nat → Option Word)
    (schedule : List (Fin n)) (s : State n) (input : List Word) (extent : n < input.length)
    (control : Control.Invariant s) (data : Data.Invariant s) (loop : Loop.Invariant s)
    (sum : ResultProof.Invariant n input s) (before : Invariant input s)
    (contract : ResultProof.ReadContract n input (runWith cfg reads schedule s).trace) :
    Invariant input (runWith cfg reads schedule s).state := by
  induction schedule generalizing reads s with
  | nil => exact before
  | cons thread rest ih =>
    obtain ⟨first,later⟩ := (ResultProof.readContract_append _ _ _ _).mp contract
    exact ih _ _ (Control.step_preserves cfg (reads 0) thread s control)
      (Data.step_preserves cfg (reads 0) s thread control data)
      (Loop.step_preserves cfg (reads 0) s thread control data loop)
      (ResultProof.step_preserves cfg (reads 0) s thread input (by omega)
        (fun t => ResultProof.shape_of_loop t _ (loop t)) sum first)
      (step_preserves cfg (reads 0) s thread input extent sum before) later

theorem reachable (cfg : Config n) (reads : Nat → Option Word) (schedule : List (Fin n))
    (input scratch : List Word) (seeds : Fin n → Seed) (extent : n < input.length)
    (contract : ResultProof.ReadContract n input
      (runWith cfg reads schedule (start input scratch seeds)).trace) :
    Invariant input (runWith cfg reads schedule (start input scratch seeds)).state :=
  runWith_preserves cfg reads schedule _ input extent
    (Control.initial input scratch seeds) (Data.initial input scratch seeds)
    (Loop.initial input scratch seeds) (ResultProof.initial input scratch seeds)
    (initial input scratch seeds) contract

/-- PC1 is reached only after the actual output store succeeded. The persistent
arena then contains exactly that writeback, retaining every other input/tail word. -/
theorem output_reached (cfg : Config n) (reads : Nat → Option Word) (schedule : List (Fin n))
    (input scratch : List Word) (seeds : Fin n → Seed) (extent : n < input.length)
    (contract : ResultProof.ReadContract n input
      (runWith cfg reads schedule (start input scratch seeds)).trace)
    (thread : Fin n)
    (block : ((runWith cfg reads schedule (start input scratch seeds)).state.lanes thread).block = .output)
    (pc : ((runWith cfg reads schedule (start input scratch seeds)).state.lanes thread).scalar.pc = 1) :
    (runWith cfg reads schedule (start input scratch seeds)).state.global = input.set n (total input n) :=
  (reachable cfg reads schedule input scratch seeds extent contract).2 thread block pc

/-- Completion of the actual leader forces the exact persistent global result;
no output event, successful store or expected final state is assumed. -/
theorem halted_leader (cfg : Config n) (reads : Nat → Option Word) (schedule : List (Fin n))
    (input scratch : List Word) (seeds : Fin n → Seed) (extent : n < input.length)
    (contract : ResultProof.ReadContract n input
      (runWith cfg reads schedule (start input scratch seeds)).trace)
    (leader : Fin n) (zero : leader.val = 0)
    (halted : ((runWith cfg reads schedule (start input scratch seeds)).state.lanes leader).halted = true) :
    (runWith cfg reads schedule (start input scratch seeds)).state.global = input.set n (total input n) := by
  obtain ⟨block,pc⟩ := Loop.halted_leader cfg reads schedule input scratch seeds leader zero halted
  exact output_reached cfg reads schedule input scratch seeds extent contract leader block pc

end Ptx.Scalar.SharedReduction.Machine.Writeback

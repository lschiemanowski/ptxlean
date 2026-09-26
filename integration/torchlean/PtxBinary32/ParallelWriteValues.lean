import PtxBinary32.ParallelReplaySources

/-! Actual final arena words are determined by actual stores even when candidate
loads are free. This theorem does not impose chronological read semantics. -/
namespace Ptx.Scalar.Parallel.Replay

private def storeAt (index : Nat) (effect : Option MemoryEffect) : Option Word :=
  match effect with
  | some e => if e.kind=.store ∧ e.address.toNat/4=index then some e.value else none
  | none => none

private theorem eval_value (a next : Scalar.State) (instruction : Scalar.Instr) (occ : Scalar.Occurrence)
    (step : Scalar.eval candidate instruction a=.next next occ) (index : Nat) :
    next.memory[index]?=(storeAt index occ.memory).or a.memory[index]? := by
  cases instruction with
  | mk guard op =>
    cases op <;> cases hg : guard.eval a <;> simp only [Scalar.eval,hg,↓reduceIte] at step
    all_goals first
      | (obtain ⟨rfl,rfl⟩ := Scalar.StepResult.next.inj step; rfl)
      | contradiction
      | skip
    all_goals
      split at step
      · contradiction
      · rename_i addrIndex checked
        obtain ⟨rfl,rfl⟩ := Scalar.StepResult.next.inj step
        have safe := Scalar.addressIndex_ok_iff.mp checked
        have bound : addrIndex<a.memory.length := by simpa [← safe.2] using safe.1.2
        simp only [storeAt,Scalar.occurrence]
        first
        | rfl
        | (by_cases eq : addrIndex=index
           · subst index; simp [← safe.2,bound]
           · simp [← safe.2,eq,List.getElem?_set_ne eq])

theorem latestWrite_append (space : Space) (index : Nat) (left right : List (Event n)) :
    latestWrite space index (left++right)=(latestWrite space index right).or (latestWrite space index left) := by
  induction left with
  | nil => simp [latestWrite]
  | cons e es ih => simp [latestWrite,ih,Option.or_assoc]

private theorem scalar_value (state : State n) (t : Fin n) (seen : Option Space) (instruction : Scalar.Instr)
    (space : Space) (index : Nat) :
    (arena (arrays (scalarStep candidate t seen instruction state).state) space)[index]? =
      (latestWrite space index (scalarStep candidate t seen instruction state).events).or ((arena (arrays state) space)[index]?) := by
  cases hs : Scalar.eval candidate instruction {(state.lanes t).scalar with memory := Parallel.arena state seen} with
  | next next occ =>
    have value := eval_value _ next instruction occ hs index
    cases seen with
    | none => simp [scalarStep,hs,arrays,setLane,arena,latestWrite,writtenAt]
    | some seen =>
      cases seen <;> cases space <;> simp [Parallel.arena] at value
      all_goals simp [scalarStep,hs,arrays,setLane,arena,latestWrite,writtenAt,value]
      all_goals cases hm : occ.memory <;> simp [storeAt,hm]
  | halted next occ =>
    have empty := (Scalar.eval_halted hs).2
    cases seen with
    | none => simp [scalarStep,hs,arrays,setLane,arena,latestWrite,writtenAt,empty]
    | some seen => cases seen <;> simp [scalarStep,hs,arrays,setLane,arena,latestWrite,writtenAt,empty]
  | fault reason => simp [scalarStep,hs,latestWrite]
  | unsupported spelling => simp [scalarStep,hs,latestWrite]

private theorem barriers_no_write (space : Space) (index : Nat) (events : List (Barrier.Event n)) :
    latestWrite space index (events.map Event.barrier)=none := by
  induction events <;> simp_all [latestWrite,writtenAt]

private theorem dispatch_value (step : Dispatch cfg candidate t instruction state out) (space : Space) (index : Nat) :
    (arena (arrays out.state) space)[index]?=(latestWrite space index out.events).or ((arena (arrays state) space)[index]?) := by
  cases step with
  | localStep => exact scalar_value _ _ _ _ _ _
  | memory => exact scalar_value _ _ _ _ _ _
  | binary32 _ | exit => simp [arrays,setLane,latestWrite,writtenAt]
  | sync =>
    rename_i resource
    cases h : (Barrier.step (barrierConfig cfg state t) state.barrier (barrierRequest cfg state t resource)).disposition <;>
      simp [synchronize,h,latestWrite,arrays,barriers_no_write]

private theorem step_value (step : Step cfg code candidate t state out) (space : Space) (index : Nat) :
    (arena (arrays out.state) space)[index]?=(latestWrite space index out.events).or ((arena (arrays state) space)[index]?) := by
  have h := step.2
  split at h
  · subst out; rfl
  · split at h
    · subst out; rfl
    · split at h
      · subst out; rfl
      · exact dispatch_value h space index

/-- Covers arbitrary load candidates and arbitrary permitted FP results. -/
theorem run_value (run : Runs cfg code state events final) (space : Space) (index : Nat) :
    (arena (arrays final) space)[index]?=(latestWrite space index events).or ((arena (arrays state) space)[index]?) := by
  induction run with
  | nil => rfl
  | cons step _ ih => rw [ih,step_value step,latestWrite_append,Option.or_assoc]

end Ptx.Scalar.Parallel.Replay

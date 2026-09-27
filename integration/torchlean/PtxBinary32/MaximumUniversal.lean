import PtxBinary32.MaximumDataRun
import PtxBinary32.ParallelWriteValues
import PtxBinary32.MaximumExecution

/-! Universal stored-output correspondence, distinct from one execution witness. -/
namespace Ptx.Scalar.Parallel.Maximum

private theorem output_pointer_index (b : Bounds d) :
    (bytePointer (width d)).toNat/4=width d := by
  have fit : 4*width d<18446744073709551616 := by have := width_fits b; omega
  simp [bytePointer,BitVec.toNat_ofNat,Nat.mod_eq_of_lt fit]

private theorem written_output (d : Nat) (b : Bounds d) (global shared : List Word)
    (seeds : Fin (width d)→Scalar.State) {events : List (Event (width d))} {final : Parallel.State (width d)}
    (run : Runs (config d) (program d) (initial d global shared seeds) events final)
    (known : Stores d global events) (event : Event (width d)) (member : event ∈ events) (index : Nat) (value : Word)
    (written : Replay.writtenAt .global index event=some value) :
    index=width d ∧ value=node global d 0 := by
  obtain ⟨t,occ,address,rfl,memory,atIndex⟩ := Replay.writtenAt_some .global index event value written
  have owner := candidate_global_owner d b global shared seeds run t occ ⟨.store,address,value⟩ member memory rfl
  have addr : address=bytePointer (width d) := owner.2.1
  have idx : width d=index := by
    change address.toNat/4=index at atIndex
    rw [addr,output_pointer_index b] at atIndex
    exact atIndex
  exact ⟨idx.symm,(known t .global occ ⟨.store,address,value⟩ member memory rfl).2.2 owner.1⟩

/-- Every completed admitted candidate execution stores the same selected word.
Schedules and candidate loads remain universally quantified. -/
theorem completed_maximum (d : Nat) (b : Bounds d) (global shared : List Word)
    (seeds : Fin (width d)→Scalar.State) {events : List (Event (width d))} {final : Parallel.State (width d)}
    (run : Runs (config d) (program d) (initial d global shared seeds) events final)
    (halted : ∀ t, (final.lanes t).halted=true) (source co) (valid : Admitted d b global shared seeds run source co) :
    final.global[width d]?=some (node global d 0) ∧
    (∀ i, i<width d → final.global[i]?=global[i]?) ∧
    final.global.length=global.length ∧ final.shared.length=shared.length ∧
    (∀ event ∈ events, AccessSafe (initial d global shared seeds) event) := by
  have known := (run_data d b global shared seeds run halted source co valid).2
  refine ⟨?_,?_,(runs_memory_length run).1,(runs_memory_length run).2,runs_access_safe run⟩
  · have finalValue := Replay.run_value run .global (width d)
    dsimp [Replay.arena,Replay.arrays,initial] at finalValue
    cases last : Replay.latestWrite .global (width d) events with
    | none =>
      let t : Fin (width d) := ⟨0,Nat.two_pow_pos _⟩
      obtain ⟨p,occ,effect,atP,pc,memory,store,addr⟩ := completed_output_store d b global shared seeds run t (halted t) rfl
      have absent := (Replay.latestWrite_none .global (width d) events).mp last _ (List.mem_of_getElem? atP)
      have fit : 4*width d<18446744073709551616 := by have := width_fits b; omega
      simp [Replay.writtenAt,memory,store,addr,bytePointer,BitVec.toNat_ofNat,Nat.mod_eq_of_lt fit] at absent
    | some value =>
      obtain ⟨before,event,after,split,written,_⟩ := Replay.latestWrite_origin .global _ events value last
      have member : event ∈ events := by simp [split]
      obtain ⟨_,correct⟩ := written_output d b global shared seeds run known event member _ value written
      simpa [last,correct] using finalValue
  · intro i hi
    have finalValue := Replay.run_value run .global i
    dsimp [Replay.arena,Replay.arrays,initial] at finalValue
    cases last : Replay.latestWrite .global i events with
    | none => simpa [last] using finalValue
    | some value =>
      obtain ⟨before,event,after,split,written,_⟩ := Replay.latestWrite_origin .global i events value last
      have member : event ∈ events := by simp [split]
      obtain ⟨idx,_⟩ := written_output d b global shared seeds run known event member i value written
      omega

/-- Finite input interpretation turns the stored word into an attained real maximum. -/
theorem completed_real_maximum (d : Nat) (b : Bounds d) (global shared : List Word)
    (seeds : Fin (width d)→Scalar.State) {events : List (Event (width d))} {final : Parallel.State (width d)}
    (run : Runs (config d) (program d) (initial d global shared seeds) events final)
    (halted : ∀ t, (final.lanes t).halted=true) (source co) (valid : Admitted d b global shared seeds run source co)
    (values : Nat→ℝ) (finite : ∀ i, i<width d → Ptx.Binary32.finiteReal (global[i]!) = some (values i)) :
    ∃ result m, final.global[width d]?=some result ∧ Ptx.Binary32.finiteReal result=some m ∧
      (∀ i, i<width d → values i≤m) ∧ ∃ i, i<width d ∧ result=global[i]! ∧ m=values i := by
  obtain ⟨m,real,upper,i,hi,wordEq,valueEq⟩ := Ptx.Binary32.Maximum.Tree.root_maximum (fun i => global[i]!) values d finite
  exact ⟨node global d 0,m,(completed_maximum d b global shared seeds run halted source co valid).1,real,upper,i,hi,wordEq,valueEq⟩

/-- The actual stored maximum supplies each score's shifted-exponential contract.
This composes interfaces, without asserting execution of a combined softmax kernel. -/
theorem completed_shifted_bounds (d : Nat) (b : Bounds d) (global shared : List Word)
    (seeds : Fin (width d)→Scalar.State) {events : List (Event (width d))} {final : Parallel.State (width d)}
    (run : Runs (config d) (program d) (initial d global shared seeds) events final)
    (halted : ∀ t, (final.lanes t).halted=true) (source co) (valid : Admitted d b global shared seeds run source co)
    (values : Nat→ℝ) (finite : ∀ i, i<width d → Ptx.Binary32.finiteReal (global[i]!) = some (values i))
    (small : ∀ i, i<width d → |values i|≤(2:ℝ)^(124:ℤ)) :
    ∃ result m, final.global[width d]?=some result ∧ Ptx.Binary32.finiteReal result=some m ∧
      (∀ i, i<width d → Ptx.Binary32.ShiftedExp.InputBounds (values i) m) ∧
      ∃ i, i<width d ∧ result=global[i]! ∧ m=values i := by
  obtain ⟨m,real,bounds,i,hi,wordEq,valueEq⟩ :=
    Ptx.Binary32.Maximum.Tree.root_shifted_bounds (fun i => global[i]!) values d finite small
  exact ⟨node global d 0,m,(completed_maximum d b global shared seeds run halted source co valid).1,
    real,bounds,i,hi,wordEq,valueEq⟩

end Ptx.Scalar.Parallel.Maximum

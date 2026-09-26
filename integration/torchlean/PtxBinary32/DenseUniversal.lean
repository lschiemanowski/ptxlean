import PtxBinary32.DenseDataRun
import PtxBinary32.ParallelWriteValues
import PtxBinary32.DenseLaunch

/-! Universal stored-output correspondence for completed admitted executions.
This quantifies over schedules, load candidates and permitted FP results. -/
namespace Ptx.Scalar.Parallel.Dense

private theorem output_pointer_index (s : Shape) (b : Bounds s) (t : Fin s.threads) :
    (bytePointer (outputIndex s t)).toNat/4=outputIndex s t := by
  have bound := (output_indices s t).2.2
  have ar := b.arithmetic
  have fit : 4*outputIndex s t<18446744073709551616 := by omega
  simp [bytePointer,BitVec.toNat_ofNat,Nat.mod_eq_of_lt fit]

private theorem written_output (s : Shape) (b : Bounds s) (global shared : List Word)
    (seeds : Fin s.threads → Scalar.State) {events : List (Event s.threads)} {final : Parallel.State s.threads}
    (run : Runs (config s b) (program s) (initial s global shared seeds) events final)
    (known : Stores s global events) (event : Event s.threads) (member : event ∈ events) (index : Nat) (value : Word)
    (written : Replay.writtenAt .global index event=some value) :
    ∃ row, row<s.rows ∧ index=s.outputBase+row ∧ Output s global row value := by
  obtain ⟨t,occ,address,rfl,memory,atIndex⟩ := Replay.writtenAt_some .global index event value written
  have owner := candidate_global_owner s b global shared seeds run t occ ⟨.store,address,value⟩ member memory rfl
  have addr : address=bytePointer (outputIndex s t) := owner.2.1
  have idx : outputIndex s t=index := by simpa [addr,output_pointer_index s b t] using atIndex
  refine ⟨t.val/s.width,(coordinates s t).1,?_,?_⟩
  · rw [← idx]; simp [outputIndex,Nat.add_comm]
  · exact (known t .global occ ⟨.store,address,value⟩ member memory rfl).2.2 owner.1

/-- All completed admitted candidate executions store a permitted evaluation of
the ordered arithmetic tree and ReLU. This is stronger than an execution witness. -/
theorem completed_forward (s : Shape) (b : Bounds s) (global shared : List Word)
    (seeds : Fin s.threads → Scalar.State) {events : List (Event s.threads)} {final : Parallel.State s.threads}
    (run : Runs (config s b) (program s) (initial s global shared seeds) events final)
    (halted : ∀ t, (final.lanes t).halted=true) (source co) (valid : Admitted s b global shared seeds run source co) :
    (∀ row : Fin s.rows, ∃ value, final.global[s.outputBase+row.val]?=some value ∧ Output s global row.val value) ∧
    (∀ i, i<s.outputBase → final.global[i]?=global[i]?) ∧
    final.global.length=global.length ∧ final.shared.length=shared.length ∧
    (∀ event ∈ events, AccessSafe (initial s global shared seeds) event) := by
  have known := (run_data s b global shared seeds run halted source co valid).2
  refine ⟨?_,?_,(runs_memory_length run).1,(runs_memory_length run).2,runs_access_safe run⟩
  · intro row
    have finalValue := Replay.run_value run .global (s.outputBase+row.val)
    dsimp [Replay.arena,Replay.arrays,initial] at finalValue
    cases last : Replay.latestWrite .global (s.outputBase+row.val) events with
    | none =>
      let t : Fin s.threads := ⟨s.thread row.val 0,thread_bound s row.val 0 row.isLt (width_positive s)⟩
      have leader : t.val%s.width=0 := by simp [t,Shape.thread]
      have index : outputIndex s t=s.outputBase+row.val := by
        simp [outputIndex,t,Shape.thread,width_positive,Nat.add_comm]
      obtain ⟨p,occ,effect,atP,pc,memory,store,addr⟩ := completed_output_store s b global shared seeds run t (halted t) leader
      rw [index] at addr
      have absent := (Replay.latestWrite_none .global (s.outputBase+row.val) events).mp last _ (List.mem_of_getElem? atP)
      have fit : 4*(s.outputBase+row.val)<18446744073709551616 := by
        have ar := b.arithmetic
        unfold Shape.globalWords at ar
        omega
      simp [Replay.writtenAt,memory,store,addr,bytePointer,BitVec.toNat_ofNat,Nat.mod_eq_of_lt fit] at absent
    | some value =>
      obtain ⟨before,event,after,split,written,_⟩ := Replay.latestWrite_origin .global _ events value last
      have member : event ∈ events := by simp [split]
      obtain ⟨r,hr,idx,correct⟩ := written_output s b global shared seeds run known event member _ value written
      have same : r=row.val := by omega
      exact ⟨value,by simpa [last] using finalValue,by simpa [same] using correct⟩
  · intro i hi
    have finalValue := Replay.run_value run .global i
    dsimp [Replay.arena,Replay.arrays,initial] at finalValue
    cases last : Replay.latestWrite .global i events with
    | none => simpa [last] using finalValue
    | some value =>
      obtain ⟨before,event,after,split,written,_⟩ := Replay.latestWrite_origin .global i events value last
      have member : event ∈ events := by simp [split]
      obtain ⟨r,_,idx,_⟩ := written_output s b global shared seeds run known event member i value written
      omega

end Ptx.Scalar.Parallel.Dense

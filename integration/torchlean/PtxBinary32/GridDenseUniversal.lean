import PtxBinary32.GridDenseDataRun

/-! Stored-output correspondence for every completed admitted row-distributed
execution. Admission/execution existence is a separate obligation. -/
namespace Ptx.Scalar.Parallel.GridDense
open Ptx.Scalar.Parallel.Dense

private theorem output_pointer_index (s : Dense.Shape) (b : Bounds s) (t : Fin s.threads) :
    (bytePointer (outputIndex s t)).toNat/4=outputIndex s t := by
  have bound := (output_indices s t).2.2
  have ar := b.arithmetic.arithmetic
  have fit : 4*outputIndex s t<18446744073709551616 := by omega
  simp [bytePointer,BitVec.toNat_ofNat,Nat.mod_eq_of_lt fit]

private theorem written_output (s : Dense.Shape) (b : Bounds s) (global : List Word)
    (seeds : Fin s.threads → Scalar.State) {events : List (Grid.Event s.rows s.width)} {final : Grid.State s.rows s.width}
    (run : Grid.Runs (config s b) (program s) (initial s global seeds) events final)
    (known : Stores s global events) (g : Fin s.rows) (event : Event s.width) (member : (g,event) ∈ events)
    (index : Nat) (value : Word) (written : Replay.writtenAt .global index event=some value) :
    index=s.outputBase+g.val ∧ Output s global g.val value := by
  obtain ⟨t,occ,address,rfl,memory,atIndex⟩ := Replay.writtenAt_some .global index event value written
  have owner := candidate_global_owner s b global seeds run g t occ ⟨.store,address,value⟩ member memory rfl
  have addr : address=bytePointer (outputIndex s (thread s g t)) := owner.2.1
  have idx : outputIndex s (thread s g t)=index := by simpa [addr,output_pointer_index s b] using atIndex
  constructor
  · rw [← idx]; simp [outputIndex,(thread_coordinates s g t).1,Nat.add_comm]
  · simpa [(thread_coordinates s g t).1] using (known g t .global occ ⟨.store,address,value⟩ member memory rfl).2.2 owner.1

/-- Universal forward correctness over actual shared-global grid interleavings.
No load value, producer correctness or noninterference premise is supplied. -/
theorem completed_forward (s : Dense.Shape) (b : Bounds s) (global : List Word)
    (seeds : Fin s.threads → Scalar.State) {events : List (Grid.Event s.rows s.width)} {final : Grid.State s.rows s.width}
    (run : Grid.Runs (config s b) (program s) (initial s global seeds) events final)
    (halted : ∀ g t, ((final.blocks g).lanes t).halted=true) (source co)
    (valid : Admitted s global seeds events source co) :
    (∀ row : Fin s.rows, ∃ value, final.global[s.outputBase+row.val]?=some value ∧ Output s global row.val value) ∧
    (∀ i, i<s.outputBase → final.global[i]?=global[i]?) ∧
    final.global.length=global.length ∧ (∀ g, (final.blocks g).shared.length=s.sharedWords) ∧
    (∀ event ∈ events, Grid.AccessSafe (initial s global seeds) event) := by
  have known := (run_data s b global seeds run halted source co valid).2
  have lengths := Grid.runs_lengths run
  refine ⟨?_,?_,lengths.1,?_,Grid.runs_access_safe run⟩
  · intro row
    have finalValue := Grid.run_global_value run (s.outputBase+row.val)
    dsimp [initial,Grid.latestGlobal] at finalValue
    cases last : Replay.latestWrite .global (s.outputBase+row.val) (events.map Prod.snd) with
    | none =>
      let t : Fin s.width := ⟨0,width_positive s⟩
      have leader : (thread s row t).val%s.width=0 := by simpa [t] using (thread_coordinates s row t).2
      have index : outputIndex s (thread s row t)=s.outputBase+row.val := by simp [outputIndex,(thread_coordinates s row t).1,Nat.add_comm]
      obtain ⟨p,occ,effect,atP,pc,memory,store,addr⟩ := completed_output_store s b global seeds run row t (halted row t) leader
      rw [index] at addr
      have member : .scalar t (some .global) occ ∈ events.map Prod.snd := List.mem_map.mpr ⟨_,List.mem_of_getElem? atP,rfl⟩
      have absent := (Replay.latestWrite_none .global (s.outputBase+row.val) (events.map Prod.snd)).mp last _ member
      have fit : 4*(s.outputBase+row.val)<18446744073709551616 := by
        have ar := b.arithmetic.arithmetic
        unfold Shape.globalWords at ar
        have hr := row.isLt
        omega
      simp [Replay.writtenAt,memory,store,addr,bytePointer,BitVec.toNat_ofNat,Nat.mod_eq_of_lt fit] at absent
    | some value =>
      obtain ⟨before,event,after,split,written,_⟩ := Replay.latestWrite_origin .global _ (events.map Prod.snd) value last
      have member : event ∈ events.map Prod.snd := by simp [split]
      obtain ⟨⟨g,e⟩,inside,rfl⟩ := List.mem_map.mp member
      obtain ⟨idx,correct⟩ := written_output s b global seeds run known g e inside _ value written
      have same : g.val=row.val := by omega
      exact ⟨value,by simpa [last] using finalValue,by simpa [same] using correct⟩
  · intro i hi
    have finalValue := Grid.run_global_value run i
    dsimp [initial,Grid.latestGlobal] at finalValue
    cases last : Replay.latestWrite .global i (events.map Prod.snd) with
    | none => simpa [last] using finalValue
    | some value =>
      obtain ⟨before,event,after,split,written,_⟩ := Replay.latestWrite_origin .global i (events.map Prod.snd) value last
      have member : event ∈ events.map Prod.snd := by simp [split]
      obtain ⟨⟨g,e⟩,inside,rfl⟩ := List.mem_map.mp member
      have idx := (written_output s b global seeds run known g e inside i value written).1
      omega
  · intro g; simpa [initial] using lengths.2 g

end Ptx.Scalar.Parallel.GridDense

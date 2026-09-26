import PtxBinary32.DenseReadSources

/-! The global operand slices cannot be overwritten by any candidate execution.
Memory admission therefore fixes all actual global reads to initialization. -/
namespace Ptx.Scalar.Parallel.Dense
open Ptx.TraceMemory

theorem global_load_index (s : Shape) (b : Bounds s) (global shared : List Word)
    (seeds : Fin s.threads → Scalar.State) {events : List (Event s.threads)} {final : Parallel.State s.threads}
    (run : Runs (config s b) (program s) (initial s global shared seeds) events final)
    (t : Fin s.threads) (occ : Scalar.Occurrence) (effect : MemoryEffect)
    (member : .scalar t (some .global) occ ∈ events) (memory : occ.memory=some effect) (load : effect.kind=.load) :
    ∃ i, i<s.outputBase ∧ effect.address=bytePointer i := by
  rcases candidate_load_address s b global shared seeds run t .global occ effect member memory load with
    ⟨weight,_,_,active,addr⟩ | ⟨_,_,_,_,sp,_⟩ | ⟨bias,_,sp,_,addr⟩
  · have slice := global_slices s _ _ (coordinates s t).1 active
    cases weight
    · exact ⟨_,by simp only [Bool.false_eq_true,↓reduceIte]; have := b.nonempty; simp only [Shape.weightBase,Shape.biasBase,Shape.outputBase] at *; omega,addr⟩
    · exact ⟨_,by simp only [↓reduceIte]; unfold Shape.outputBase; omega,addr⟩
  · cases sp
  · cases bias
    · cases sp
    · exact ⟨_,(output_indices s t).2.1,addr⟩

/-- A noninitial graph write is never in the global operand prefix. -/
theorem global_prefix_unwritten (s : Shape) (b : Bounds s) (global shared : List Word)
    (seeds : Fin s.threads → Scalar.State) {events : List (Event s.threads)} {final : Parallel.State s.threads}
    (run : Runs (config s b) (program s) (initial s global shared seeds) events final)
    (source co) (w : Fin (Memory.labels (program s) global shared events).length)
    (write : (Memory.graph (program s) global shared events source co).write w)
    (noninitial : ¬(Memory.graph (program s) global shared events source co).initial w)
    (i : Nat) (hi : i<s.outputBase) :
    ((Memory.graph (program s) global shared events source co).event w).effect.address ≠
      (⟨0,i⟩ : Location 2).code := by
  intro eq
  obtain ⟨t,p,space,occ,effect,atP,_,_,memory,store,label⟩ :=
    Memory.program_write_origin (program s) global shared events source co w write noninitial
  have loc : Memory.location space effect.address=(⟨0,i⟩ : Location 2) := by
    apply Location.code_injective
    simpa [label,Memory.ofEffect,Access.effect] using eq
  cases space with
  | shared => have h := congrArg Location.storage loc; simp [Memory.location,Memory.slot] at h
  | global =>
    have addr := (candidate_global_owner s b global shared seeds run t occ effect (List.mem_of_getElem? atP) memory store).2.1
    have bound := (output_indices s t).2.2
    have arithmetic := b.arithmetic
    have fit : 4*outputIndex s t<18446744073709551616 := by omega
    have index := congrArg Location.word loc
    simp [Memory.location,addr,bytePointer,BitVec.toNat_ofNat,Nat.mod_eq_of_lt fit] at index
    have lower : s.outputBase ≤ outputIndex s t := Nat.le_add_left _ _
    omega

/-- An admitted global load observes the original input, weight or bias word.
Neither source identity nor the value is a premise. -/
theorem global_read_source (s : Shape) (b : Bounds s) (global shared : List Word)
    (seeds : Fin s.threads → Scalar.State) {events : List (Event s.threads)} {final : Parallel.State s.threads}
    (run : Runs (config s b) (program s) (initial s global shared seeds) events final)
    (source co) (valid : Admitted s b global shared seeds run source co)
    (q : Nat) (t : Fin s.threads) (occ : Scalar.Occurrence) (effect : MemoryEffect)
    (atQ : events[q]?=some (.scalar t (some .global) occ))
    (memory : occ.memory=some effect) (load : effect.kind=.load) :
    ∃ i, i<s.outputBase ∧ i<global.length ∧ effect.address=bytePointer i ∧ effect.value=global[i]! := by
  obtain ⟨i,hi,addr⟩ := global_load_index s b global shared seeds run t occ effect (List.mem_of_getElem? atQ) memory load
  obtain ⟨r,label⟩ := Memory.run_graph_complete run source co q t .global occ effect atQ memory
  dsimp [initial] at label
  let g := Memory.graph (program s) global shared events source co
  have read : g.read r := by simp [g,Graph.read,label,Memory.ofEffect,Access.effect,AccessKind.op,load]
  obtain ⟨write,same,value⟩ := valid.sources.compatible r read
  have bound := b.arithmetic
  have fit : 4*i<18446744073709551616 := by unfold Shape.globalWords at bound; omega
  have address : (g.event (source r)).effect.address=(⟨0,i⟩ : Location 2).code := by
    change (g.event (source r)).effect.address=(g.event r).effect.address at same
    rw [same]
    simp [g,label,Memory.ofEffect,Access.effect,Memory.location,Memory.slot,addr,bytePointer,BitVec.toNat_ofNat,Nat.mod_eq_of_lt fit]
  have init : g.initial (source r) := by
    by_contra no
    exact global_prefix_unwritten s b global shared seeds run source co _ write no i hi address
  have member : g.event (source r) ∈ Memory.labels (program s) global shared events := List.getElem_mem _
  obtain ⟨entry,inside,entryEq⟩ := Memory.Chronology.initial_origin member ((Memory.Chronology.initial_iff member).mp init)
  have location : entry.location=(⟨0,i⟩ : Location 2) := by
    apply Location.code_injective
    simpa [entryEq,Initial.occurrence] using address
  obtain ⟨length,entryValue⟩ := SharedReduction.Machine.Memory.initial_global global shared entry i inside location
  refine ⟨i,hi,length,addr,?_⟩
  change (g.event (source r)).effect.value=(g.event r).effect.value at value
  rw [entryEq] at value
  simpa [g,label,Memory.ofEffect,Access.effect,Initial.occurrence,entryValue] using value.symm

end Ptx.Scalar.Parallel.Dense

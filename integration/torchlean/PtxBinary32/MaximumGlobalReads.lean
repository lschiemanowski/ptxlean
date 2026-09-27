import PtxBinary32.MaximumReadSources

/-! The global input words cannot be overwritten by any candidate execution.
Memory admission therefore fixes all actual global reads to initialization. -/
namespace Ptx.Scalar.Parallel.Maximum
open Ptx.TraceMemory

theorem global_load_index (d : Nat) (b : Bounds d) (global shared : List Word)
    (seeds : Fin (width d) → Scalar.State) {events : List (Event (width d))} {final : Parallel.State (width d)}
    (run : Runs (config d) (program d) (initial d global shared seeds) events final)
    (t : Fin (width d)) (occ : Scalar.Occurrence) (effect : MemoryEffect)
    (member : .scalar t (some .global) occ ∈ events) (memory : occ.memory=some effect) (load : effect.kind=.load) :
    ∃ i, i<width d ∧ effect.address=bytePointer i := by
  rcases candidate_load_address d b global shared seeds run t .global occ effect member memory load with
    ⟨_,_,addr⟩ | ⟨_,_,_,_,sp,_⟩ | ⟨_,sp,_⟩
  · exact ⟨t.val,t.isLt,addr⟩
  · cases sp
  · cases sp

/-- A noninitial graph write is never in the global operand prefix. -/
theorem global_prefix_unwritten (d : Nat) (b : Bounds d) (global shared : List Word)
    (seeds : Fin (width d) → Scalar.State) {events : List (Event (width d))} {final : Parallel.State (width d)}
    (run : Runs (config d) (program d) (initial d global shared seeds) events final)
    (source co) (w : Fin (Memory.labels (program d) global shared events).length)
    (write : (Memory.graph (program d) global shared events source co).write w)
    (noninitial : ¬(Memory.graph (program d) global shared events source co).initial w)
    (i : Nat) (hi : i<width d) :
    ((Memory.graph (program d) global shared events source co).event w).effect.address ≠
      (⟨0,i⟩ : Location 2).code := by
  intro eq
  obtain ⟨t,p,space,occ,effect,atP,_,_,memory,store,label⟩ :=
    Memory.program_write_origin (program d) global shared events source co w write noninitial
  have loc : Memory.location space effect.address=(⟨0,i⟩ : Location 2) := by
    apply Location.code_injective
    simpa [label,Memory.ofEffect,Access.effect] using eq
  cases space with
  | shared => have h := congrArg Location.storage loc; simp [Memory.location,Memory.slot] at h
  | global =>
    have addr := (candidate_global_owner d b global shared seeds run t occ effect (List.mem_of_getElem? atP) memory store).2.1
    have bound := width_fits b
    have fit : 4*width d<18446744073709551616 := by omega
    have index := congrArg Location.word loc
    simp [Memory.location,addr,bytePointer,BitVec.toNat_ofNat,Nat.mod_eq_of_lt fit] at index
    omega

/-- An admitted global load observes the original input word.
Neither source identity nor the value is a premise. -/
theorem global_read_source (d : Nat) (b : Bounds d) (global shared : List Word)
    (seeds : Fin (width d) → Scalar.State) {events : List (Event (width d))} {final : Parallel.State (width d)}
    (run : Runs (config d) (program d) (initial d global shared seeds) events final)
    (source co) (valid : Admitted d b global shared seeds run source co)
    (q : Nat) (t : Fin (width d)) (occ : Scalar.Occurrence) (effect : MemoryEffect)
    (atQ : events[q]?=some (.scalar t (some .global) occ))
    (memory : occ.memory=some effect) (load : effect.kind=.load) :
    ∃ i, i<width d ∧ i<global.length ∧ effect.address=bytePointer i ∧ effect.value=global[i]! := by
  obtain ⟨i,hi,addr⟩ := global_load_index d b global shared seeds run t occ effect (List.mem_of_getElem? atQ) memory load
  obtain ⟨r,label⟩ := Memory.run_graph_complete run source co q t .global occ effect atQ memory
  dsimp [initial] at label
  let g := Memory.graph (program d) global shared events source co
  have read : g.read r := by simp [g,Graph.read,label,Memory.ofEffect,Access.effect,AccessKind.op,load]
  obtain ⟨write,same,value⟩ := valid.sources.compatible r read
  have bound := width_fits b
  have fit : 4*i<18446744073709551616 := by omega
  have address : (g.event (source r)).effect.address=(⟨0,i⟩ : Location 2).code := by
    change (g.event (source r)).effect.address=(g.event r).effect.address at same
    rw [same]
    simp [g,label,Memory.ofEffect,Access.effect,Memory.location,Memory.slot,addr,bytePointer,BitVec.toNat_ofNat,Nat.mod_eq_of_lt fit]
  have init : g.initial (source r) := by
    by_contra no
    exact global_prefix_unwritten d b global shared seeds run source co _ write no i hi address
  have member : g.event (source r) ∈ Memory.labels (program d) global shared events := List.getElem_mem _
  obtain ⟨entry,inside,entryEq⟩ := Memory.Chronology.initial_origin member ((Memory.Chronology.initial_iff member).mp init)
  have location : entry.location=(⟨0,i⟩ : Location 2) := by
    apply Location.code_injective
    simpa [entryEq,Initial.occurrence] using address
  obtain ⟨length,entryValue⟩ := SharedReduction.Machine.Memory.initial_global global shared entry i inside location
  refine ⟨i,hi,length,addr,?_⟩
  change (g.event (source r)).effect.value=(g.event r).effect.value at value
  rw [entryEq] at value
  simpa [g,label,Memory.ofEffect,Access.effect,Initial.occurrence,entryValue] using value.symm

end Ptx.Scalar.Parallel.Maximum

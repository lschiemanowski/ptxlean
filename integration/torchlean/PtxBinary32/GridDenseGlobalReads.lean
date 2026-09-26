import PtxBinary32.GridDenseOwnership

/-! The global operand slices cannot be overwritten by any candidate execution.
Memory admission therefore fixes all actual global reads to initialization. -/
namespace Ptx.Scalar.Parallel.GridDense
open Ptx.Scalar.Parallel.Dense
open Ptx.TraceMemory (Location Access Initial AccessKind)

theorem global_load_index (s : Dense.Shape) (b : Bounds s) (global : List Word)
    (seeds : Fin s.threads → Scalar.State) {events : List (Grid.Event s.rows s.width)} {final : Grid.State s.rows s.width}
    (run : Grid.Runs (config s b) (program s) (initial s global seeds) events final)
    (group : Fin s.rows) (t : Fin s.width) (occ : Scalar.Occurrence) (effect : MemoryEffect)
    (member : (group,.scalar t (some .global) occ) ∈ events) (memory : occ.memory=some effect) (load : effect.kind=.load) :
    ∃ i, i<s.outputBase ∧ effect.address=bytePointer i := by
  rcases candidate_load_address s b global seeds run group t .global occ effect member memory load with
    ⟨weight,_,_,active,addr⟩ | ⟨_,_,_,_,sp,_⟩ | ⟨bias,_,sp,_,addr⟩
  · have slice := global_slices s _ _ (coordinates s (thread s group t)).1 active
    cases weight
    · exact ⟨_,by simp only [Bool.false_eq_true,↓reduceIte]; have := group.isLt; simp only [Shape.weightBase,Shape.biasBase,Shape.outputBase] at *; omega,addr⟩
    · exact ⟨_,by simp only [↓reduceIte]; unfold Shape.outputBase; omega,addr⟩
  · cases sp
  · cases bias
    · cases sp
    · exact ⟨_,(output_indices s (thread s group t)).2.1,addr⟩

/-- A noninitial graph write is never in the global operand prefix. -/
theorem global_prefix_unwritten (s : Dense.Shape) (b : Bounds s) (global : List Word)
    (seeds : Fin s.threads → Scalar.State) {events : List (Grid.Event s.rows s.width)} {final : Grid.State s.rows s.width}
    (run : Grid.Runs (config s b) (program s) (initial s global seeds) events final)
    (source co) (w : Fin (Grid.Memory.labels (program s) (initial s global seeds) events).length)
    (write : (Grid.Memory.graph (program s) (initial s global seeds) events source co).write w)
    (noninitial : ¬(Grid.Memory.graph (program s) (initial s global seeds) events source co).initial w)
    (i : Nat) (hi : i<s.outputBase) :
    ((Grid.Memory.graph (program s) (initial s global seeds) events source co).event w).effect.address ≠
      (⟨0,i⟩ : Location (s.rows+1)).code := by
  intro eq
  obtain ⟨group,t,p,space,occ,effect,atP,_,_,memory,store,label⟩ :=
    Grid.Memory.program_write_origin (program s) (initial s global seeds) events source co w write noninitial
  have loc : Grid.location group space effect.address=(⟨0,i⟩ : Location (s.rows+1)) := by
    apply Location.code_injective
    simpa [label,Grid.Memory.ofEffect,Access.effect] using eq
  cases space with
  | shared => have h := congrArg Location.storage loc; simp [Grid.location] at h
  | global =>
    have addr := (candidate_global_owner s b global seeds run group t occ effect (List.mem_of_getElem? atP) memory store).2.1
    have bound := (output_indices s (thread s group t)).2.2
    have arithmetic := b.arithmetic.arithmetic
    have fit : 4*outputIndex s (thread s group t)<18446744073709551616 := by omega
    have index := congrArg Location.word loc
    simp [Grid.location,addr,bytePointer,BitVec.toNat_ofNat,Nat.mod_eq_of_lt fit] at index
    have lower : s.outputBase ≤ outputIndex s (thread s group t) := Nat.le_add_left _ _
    omega

/-- An admitted global load observes the original input, weight or bias word.
Neither source identity nor the value is a premise. -/
theorem global_read_source (s : Dense.Shape) (b : Bounds s) (global : List Word)
    (seeds : Fin s.threads → Scalar.State) {events : List (Grid.Event s.rows s.width)} {final : Grid.State s.rows s.width}
    (run : Grid.Runs (config s b) (program s) (initial s global seeds) events final)
    (source co) (valid : Graph.Ordered.Valid (Grid.Memory.graph (program s) (initial s global seeds) events source co) (Grid.Memory.cross (program s) (initial s global seeds) events))
    (q : Nat) (group : Fin s.rows) (t : Fin s.width) (occ : Scalar.Occurrence) (effect : MemoryEffect)
    (atQ : events[q]?=some (group,.scalar t (some .global) occ))
    (memory : occ.memory=some effect) (load : effect.kind=.load) :
    ∃ i, i<s.outputBase ∧ i<global.length ∧ effect.address=bytePointer i ∧ effect.value=global[i]! := by
  obtain ⟨i,hi,addr⟩ := global_load_index s b global seeds run group t occ effect (List.mem_of_getElem? atQ) memory load
  obtain ⟨r,label⟩ := Grid.Memory.graph_complete run source co q group t .global occ effect atQ memory
  let g := Grid.Memory.graph (program s) (initial s global seeds) events source co
  have read : g.read r := by simp [g,Graph.read,label,Grid.Memory.ofEffect,Access.effect,AccessKind.op,load]
  obtain ⟨write,same,value⟩ := valid.sources.compatible r read
  have bound := b.arithmetic.arithmetic
  have fit : 4*i<18446744073709551616 := by unfold Shape.globalWords at bound; omega
  have address : (g.event (source r)).effect.address=(⟨0,i⟩ : Location (s.rows+1)).code := by
    change (g.event (source r)).effect.address=(g.event r).effect.address at same
    rw [same]
    simp [g,label,Grid.Memory.ofEffect,Access.effect,Grid.location,addr,bytePointer,BitVec.toNat_ofNat,Nat.mod_eq_of_lt fit]
  have init : g.initial (source r) := by
    by_contra no
    exact global_prefix_unwritten s b global seeds run source co _ write no i hi address
  have member : g.event (source r) ∈ Grid.Memory.labels (program s) (initial s global seeds) events := List.getElem_mem _
  obtain ⟨entry,inside,entryEq⟩ := Grid.Memory.initial_origin (program s) (initial s global seeds) events _ member init
  have location : entry.location=(⟨0,i⟩ : Location (s.rows+1)) := by
    apply Location.code_injective
    simpa [entryEq,Initial.occurrence] using address
  obtain ⟨length,entryValue⟩ := Grid.Memory.initial_global (initial s global seeds) entry i inside location
  refine ⟨i,hi,length,addr,?_⟩
  change (g.event (source r)).effect.value=(g.event r).effect.value at value
  rw [entryEq,show g.event r=⟨some (Grid.Memory.threadId group t),q,(Grid.Memory.ofEffect group .global effect).effect⟩ from label] at value
  simpa [Grid.Memory.ofEffect,Access.effect,Initial.occurrence,entryValue,initial] using value.symm

end Ptx.Scalar.Parallel.GridDense

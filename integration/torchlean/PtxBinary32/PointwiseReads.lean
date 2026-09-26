import PtxBinary32.PointwiseControl

namespace Ptx.Scalar.Parallel.Pointwise
open Ptx.TraceMemory

def Admitted (op : Op) (l : Layout n) (global shared : List Word) (seeds : Fin n → Scalar.State)
    {cfg : Config n} {events : List (Event n)} {final : State n}
    (run : Runs cfg (program op) (initial l global shared seeds) events final)
    (source : Fin (Memory.labels (program op) global shared events).length → Fin (Memory.labels (program op) global shared events).length)
    (co : Fin (Memory.labels (program op) global shared events).length → Fin (Memory.labels (program op) global shared events).length → Bool) : Prop :=
  Graph.Ordered.Valid (Memory.graph (program op) global shared events source co)
    (Memory.runOrder run rfl source co).cross

theorem pointer_index (l : Layout n) (i : Nat) (bound : i<l.prefixWords+n) :
    (Dense.bytePointer i).toNat/4=i := by
  have fit : 4*i<18446744073709551616 := by have := l.small; omega
  simp [Dense.bytePointer,BitVec.toNat_ofNat,Nat.mod_eq_of_lt fit]

/-- No actual instruction writes an operand location. -/
theorem prefix_unwritten (op : Op) (l : Layout n) (global shared : List Word) (seeds : Fin n → Scalar.State)
    {cfg : Config n} {events : List (Event n)} {final : State n}
    (run : Runs cfg (program op) (initial l global shared seeds) events final)
    (source co) (w : Fin (Memory.labels (program op) global shared events).length)
    (write : (Memory.graph (program op) global shared events source co).write w)
    (noninitial : ¬(Memory.graph (program op) global shared events source co).initial w)
    (i : Nat) (hi : i<l.prefixWords) :
    ((Memory.graph (program op) global shared events source co).event w).effect.address ≠
      (⟨0,i⟩ : Location 2).code := by
  intro eq
  obtain ⟨t,p,space,occ,effect,atP,_,_,memory,store,label⟩ :=
    Memory.program_write_origin (program op) global shared events source co w write noninitial
  obtain ⟨rfl,_,addr⟩ := store_address op l global shared seeds run t space occ effect (List.mem_of_getElem? atP) memory store
  have loc : Memory.location .global effect.address=(⟨0,i⟩ : Location 2) := by
    apply Location.code_injective
    simpa [label,Memory.ofEffect,Access.effect] using eq
  have index := congrArg Location.word loc
  have bound : l.output t<l.prefixWords+n := by have := t.isLt; unfold Layout.output; omega
  simp [Memory.location,addr,pointer_index l _ bound] at index
  unfold Layout.output at index
  omega

/-- Admission forces every read to its unchanged initial operand. -/
theorem read_source (op : Op) (l : Layout n) (global shared : List Word) (seeds : Fin n → Scalar.State)
    {cfg : Config n} {events : List (Event n)} {final : State n}
    (run : Runs cfg (program op) (initial l global shared seeds) events final)
    (source co) (valid : Admitted op l global shared seeds run source co)
    (q : Nat) (t : Fin n) (space : Space) (occ : Scalar.Occurrence) (effect : MemoryEffect)
    (atQ : events[q]?=some (.scalar t (some space) occ))
    (memory : occ.memory=some effect) (load : effect.kind=.load) :
    ∃ right : Bool, occ.pc=(if right then 1 else 0) ∧
      effect.value=global[if right then l.right t else l.left t]! := by
  obtain ⟨rfl,right,pc,addr⟩ := load_address op l global shared seeds run t space occ effect (List.mem_of_getElem? atQ) memory load
  let i := if right then l.right t else l.left t
  have hi : i<l.prefixWords := by cases right <;> first | exact l.rightBound t | exact l.leftBound t
  obtain ⟨r,label⟩ := Memory.run_graph_complete run source co q t .global occ effect atQ memory
  dsimp [initial] at label
  let g := Memory.graph (program op) global shared events source co
  have read : g.read r := by simp [g,Graph.read,label,Memory.ofEffect,Access.effect,AccessKind.op,load]
  obtain ⟨write,same,value⟩ := valid.sources.compatible r read
  have address : (g.event (source r)).effect.address=(⟨0,i⟩ : Location 2).code := by
    change (g.event (source r)).effect.address=(g.event r).effect.address at same
    rw [same]
    simp [g,label,Memory.ofEffect,Access.effect,Memory.location,Memory.slot,addr,← show i=(if right then l.right t else l.left t) from rfl,pointer_index l i (by omega)]
  have init : g.initial (source r) := by
    by_contra no
    exact prefix_unwritten op l global shared seeds run source co _ write no i hi address
  have member : g.event (source r) ∈ Memory.labels (program op) global shared events := List.getElem_mem _
  obtain ⟨entry,inside,entryEq⟩ := Memory.Chronology.initial_origin member ((Memory.Chronology.initial_iff member).mp init)
  have location : entry.location=(⟨0,i⟩ : Location 2) := by
    apply Location.code_injective
    simpa [entryEq,Initial.occurrence] using address
  obtain ⟨_,entryValue⟩ := SharedReduction.Machine.Memory.initial_global global shared entry i inside location
  refine ⟨right,pc,?_⟩
  change (g.event (source r)).effect.value=(g.event r).effect.value at value
  rw [entryEq] at value
  simpa [g,label,Memory.ofEffect,Access.effect,Initial.occurrence,entryValue] using value.symm

end Ptx.Scalar.Parallel.Pointwise

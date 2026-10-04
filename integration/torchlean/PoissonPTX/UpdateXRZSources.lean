import PoissonPTX.UpdateXRZFootprint
import PoissonPTX.ObservedParallelNative
import PoissonPTX.GlobalThreadSources

namespace PtxTorchLean.Poisson.PTX.UpdateXRZ
open Concurrent
variable {n : Nat} {a : Arena n} {memory : Memory} {regs : Fin n → Registers}
  {t : Fin n → Flow.State} {words : List (Event n)} {indices : List (Fin n × IndexSources.Access)}
  {occurrence : Nat} {reader : Fin n} {ra : Access} {ia : IndexSources.Access}

/-- The numerical inputs are derived from actual admitted byte sources. All
possible overlapping stores of x or r are the same owner's later instruction. -/
theorem Arena.read_value
    (run : Flow.Parallel.Runs a.context a.program (fun i => a.start memory (regs i)) words indices t)
    (compatible : Visibility.Compatible (fun space => match space with | .global => memory | .shared => fun _ => 0) words source)
    (admitted : Visibility.GlobalThreadSources words source)
    (observed : words[occurrence]?=some (.data reader ra)) (read : ra.data.store=false) :
    ra.data.value=read64 memory ra.data.address := by
  have shape := a.parallel_access run (List.mem_of_getElem? observed)
  have global := shape.1
  simp only [read,Bool.false_eq_true,↓reduceIte] at shape
  rcases shape.2 with scalar | ⟨field,notZ,readSite,readAddress⟩
  · have readonly : Visibility.ReadOnly words ra.space ra.data.address := by
      intro w owner wa fetched store same j k overlap
      have write := a.parallel_access run (List.mem_of_getElem? fetched)
      simp only [store,↓reduceIte] at write
      obtain ⟨f,_,_,address⟩ := write.2
      have apart := a.alpha_disjoint f owner
      rw [address,scalar.2] at overlap
      have hj:=j.isLt; have hk:=k.isLt
      unfold Sources.Disjoint at apart; omega
    simpa only [global] using Visibility.read_only_value compatible observed read readonly
  · have chosen := Visibility.before_own_writes_initial compatible admitted observed read global
    apply chosen (fun w owner wa fetched store wg j k overlap => ?_) |>.2
    have write := a.parallel_access run (List.mem_of_getElem? fetched)
    simp only [store,↓reduceIte] at write
    obtain ⟨f,kind,storeSite,storeAddress⟩ := write.2
    have same := a.overlap_owner f field owner reader j k (by simpa only [storeAddress,readAddress] using overlap)
    obtain ⟨rfl,rfl⟩ := same
    refine ⟨rfl,?_,storeAddress.trans readAddress.symm⟩
    apply Flow.Parallel.before_of_pc run entry_linear observed fetched
    rw [readSite,storeSite]
    cases f <;> simp_all [readPC,storePC]

theorem Arena.index_value
    (run : Flow.Parallel.Runs a.context a.program (fun i => a.start memory (regs i)) words indices t)
    (compatible : IndexSources.Compatible memory words indices source)
    (observed : indices[occurrence]?=some (reader,ia)) : ia.value=read32 memory ia.address := by
  have address := (a.parallel_index run (List.mem_of_getElem? observed)).2
  apply IndexSources.read_only_value compatible observed
  intro w owner wa fetched store global j k overlap
  have write := a.parallel_access run (List.mem_of_getElem? fetched)
  simp only [store,↓reduceIte] at write
  obtain ⟨f,_,_,storeAddress⟩ := write.2
  have apart := a.boundary_disjoint f owner reader
  rw [storeAddress,address] at overlap
  have hj:=j.isLt; have hk:=k.isLt; omega

/-- Any store preceding a future word read touches another field. In-place
reads occur before their own stores, so they do not require false separation. -/
theorem Arena.future_apart
    (run : Flow.Parallel.Runs a.context a.program (fun i => a.start memory (regs i)) words indices t)
    (written : Event.data owner wa∈words) (store : wa.data.store=true)
    (readmem : Event.data reader ra∈words) (read : ra.data.store=false)
    (before : wa.data.pc<ra.data.pc) : Sources.Disjoint wa.data.address ra.data.address := by
  have write := a.parallel_access run written
  have load := a.parallel_access run readmem
  simp only [store,↓reduceIte] at write
  simp only [read,Bool.false_eq_true,↓reduceIte] at load
  obtain ⟨f,kind,storeSite,storeAddress⟩ := write.2
  rcases load.2 with scalar | ⟨g,notZ,readSite,readAddress⟩
  · rw [storeAddress,scalar.2]; exact a.alpha_disjoint f owner
  · rw [storeAddress,readAddress]
    apply a.owners f g owner reader
    apply Or.inl
    intro eq
    subst g
    rw [storeSite,readSite] at before
    cases f <;> simp_all [readPC,storePC]

theorem Arena.index_apart
    (run : Flow.Parallel.Runs a.context a.program (fun i => a.start memory (regs i)) words indices t)
    (written : Event.data owner wa∈words) (store : wa.data.store=true)
    (readmem : (reader,ia)∈indices) :
    wa.data.address+8≤ ia.address ∨ ia.address+4≤wa.data.address := by
  have write := a.parallel_access run written
  simp only [store,↓reduceIte] at write
  obtain ⟨f,_,_,address⟩ := write.2
  rw [address,(a.parallel_index run readmem).2]
  exact a.boundary_disjoint f owner reader

end PtxTorchLean.Poisson.PTX.UpdateXRZ

import PoissonPTX.IndexSources

namespace PtxTorchLean.Poisson.PTX.Concurrent.Relabel

/-- Counter labels may change; all accessed bytes, values and participants stay
identical. A common barrier-key renaming is used throughout the history. -/
inductive EventRelated (renameKey : Ptx.Barrier.Key → Ptx.Barrier.Key) : Event n → Event n → Prop where
  | data : EventRelated renameKey (.data thread ⟨space,⟨pc,store,byteAddress,value⟩⟩)
      (.data thread ⟨space,⟨otherPC,store,byteAddress,value⟩⟩)
  | arrival : EventRelated renameKey (.barrier (.arrival key thread)) (.barrier (.arrival (renameKey key) thread))
  | completion : EventRelated renameKey (.barrier (.completion key)) (.barrier (.completion (renameKey key)))

abbrev Related (renameKey : Ptx.Barrier.Key → Ptx.Barrier.Key) (old new : List (Event n)) :=
  List.Forall₂ (EventRelated renameKey) old new

variable {n : Nat} {old new : List (Event n)} {e : Event n} {r : Nat}

theorem at_old (related : Related renameKey old new) (observed : old[r]?=some e) :
    ∃ other, new[r]?=some other ∧ EventRelated renameKey e other := by
  induction related generalizing r with
  | nil => simp at observed
  | cons one rest ih =>
    cases r with
    | zero => simp only [List.getElem?_cons_zero,Option.some.injEq] at observed; subst e; exact ⟨_,rfl,one⟩
    | succ r => exact ih observed

theorem at_new (related : Related renameKey old new) (observed : new[r]?=some e) :
    ∃ other, old[r]?=some other ∧ EventRelated renameKey other e := by
  induction related generalizing r with
  | nil => simp at observed
  | cons one rest ih =>
    cases r with
    | zero => simp only [List.getElem?_cons_zero,Option.some.injEq] at observed; subst e; exact ⟨_,rfl,one⟩
    | succ r => exact ih observed

/-- Source admission is invariant under counter and barrier-label changes.
This direction is the one needed to use the local proof on an absolute run. -/
theorem compatible (related : Related renameKey old new)
    (admitted : Visibility.Compatible initial new source) : Visibility.Compatible initial old source := by
  intro r reader ra observed read k
  obtain ⟨other,seen,record⟩ := at_old related observed
  cases record with
  | data =>
    have h := admitted r reader _ seen read k
    cases chosen : source r k with
    | initial => simpa only [chosen] using h
    | store w j =>
      simp only [chosen] at h ⊢
      obtain ⟨writer,wa,writeSeen,store,space,address,value⟩ := h
      obtain ⟨oldWrite,oldSeen,writeRecord⟩ := at_new related writeSeen
      cases writeRecord
      exact ⟨writer,_,oldSeen,store,space,address,value⟩

theorem across (related : Related renameKey old new) (ordered : Visibility.Across old w r) :
    Visibility.Across new w r := by
  obtain ⟨writer,reader,wa,ra,key,a,c,hw,hr,ha,hc,before,middle,after⟩ := ordered
  obtain ⟨_,hw,writeRecord⟩ := at_old related hw
  obtain ⟨_,hr,readRecord⟩ := at_old related hr
  obtain ⟨_,ha,arrivalRecord⟩ := at_old related ha
  obtain ⟨_,hc,completionRecord⟩ := at_old related hc
  cases writeRecord; cases readRecord; cases arrivalRecord; cases completionRecord
  exact ⟨writer,reader,_,_,renameKey key,a,c,hw,hr,ha,hc,before,middle,after⟩

theorem performed (related : Related renameKey old new)
    (admitted : Visibility.Performed new source) : Visibility.Performed old source := by
  intro w r writer reader wa ra hw hr write read sw sr ordered j k address
  have order := across related ordered
  obtain ⟨_,hw,writeRecord⟩ := at_old related hw
  obtain ⟨_,hr,readRecord⟩ := at_old related hr
  cases writeRecord; cases readRecord
  exact admitted w r writer reader _ _ hw hr write read sw sr order j k address

theorem indices (related : Related renameKey old new)
    (admitted : IndexSources.Compatible initial new indexRecords source) :
    IndexSources.Compatible initial old indexRecords source := by
  intro r reader ra observed k
  have h := admitted r reader ra observed k
  cases chosen : source r k with
  | initial => simpa only [chosen] using h
  | store w j =>
    simp only [chosen] at h ⊢
    obtain ⟨writer,wa,writeSeen,store,space,address,value⟩ := h
    obtain ⟨oldWrite,oldSeen,writeRecord⟩ := at_new related writeSeen
    cases writeRecord
    exact ⟨writer,_,oldSeen,store,space,address,value⟩

end PtxTorchLean.Poisson.PTX.Concurrent.Relabel

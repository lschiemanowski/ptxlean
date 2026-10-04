import PoissonPTX.ByteHistory

namespace PtxTorchLean.Poisson.PTX.Concurrent.ByteHistory

/-- This stronger read policy is used only to construct a finite witness.
Universal correctness continues to use the weaker necessary source rules. -/
def Reads (initial : Space → Memory) (events : List (Event n)) : Prop :=
  ∀ r reader a, events[r]?=some (.data reader a) → a.data.store=false →
    a.data.value=read64 (publish initial (events.take r) a.space) a.data.address

def sources (events : List (Event n)) (r : Nat) (k : Fin 8) : Sources.Origin Nat :=
  match events[r]? with
  | some (.data _ a) => origin (events.take r) a.space (a.data.address+k.val)
  | _ => .initial

/-- Every witness read byte comes from initialization or an actual earlier
store. A barrier-ordered overlapping write rules out initialization. -/
theorem admitted (reads : Reads initial events) :
    Visibility.Compatible initial events (sources events) ∧ Visibility.Performed events (sources events) := by
  constructor
  · intro r reader a found read k
    have value := congrArg (fun w => byte w k.val) (reads r reader a found read)
    rw [Sources.byte_read64] at value
    have selected := origin_value (space:=a.space) (address:=a.data.address+k.val) (events.take r) initial
    simp only [sources,found]
    cases choice : origin (events.take r) a.space (a.data.address+k.val) with
    | initial =>
      simp only [choice] at selected
      exact value.trans selected
    | store w j =>
      simp only [choice] at selected
      obtain ⟨writer,wa,atStore,write,space,address,bits⟩ := selected
      have bound := (List.getElem?_eq_some_iff.mp atStore).1
      have earlier : w<r := by simp only [List.length_take] at bound; omega
      have actual : events[w]?=some (.data writer wa) := by
        simpa [List.getElem?_take,earlier] using atStore
      exact ⟨writer,wa,actual,write,space,address,value.trans bits⟩
  · intro w r writer reader wa ra hw hr write read sw sr across j k same
    obtain ⟨_,_,_,_,_,a,c,_,_,_,_,before,arrived,released⟩ := across
    have earlier : w<r := by omega
    have inPrefix : (events.take r)[w]?=some (.data writer wa) := by
      simp [earlier,hw]
    have cover : Covers (.data writer wa) ra.space (ra.data.address+k.val) := by
      refine ⟨writer,wa,rfl,write,sw.trans sr.symm,?_,?_⟩
      all_goals have := j.isLt; omega
    simp only [sources,hr]
    intro initialSource
    exact (origin_initial (events.take r)).mp initialSource _ (List.mem_of_getElem? inPrefix) cover

/-- The selected store is always strictly earlier than the read, even when
several stores overlap different bytes of the same word. -/
theorem source_earlier
    (found : events[r]?=some (.data reader a))
    (selected : sources events r k=.store w j) : w<r := by
  have value := origin_value (space:=a.space) (address:=a.data.address+k.val) (events.take r) (fun _ _ => 0)
  simp only [sources,found] at selected
  rw [selected] at value
  obtain ⟨_,_,atStore,_⟩ := value
  have bound := (List.getElem?_eq_some_iff.mp atStore).1
  simp only [List.length_take] at bound
  omega

end PtxTorchLean.Poisson.PTX.Concurrent.ByteHistory

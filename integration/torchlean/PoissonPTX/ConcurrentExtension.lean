import PoissonPTX.CellWordView

namespace PtxTorchLean.Poisson.PTX.Concurrent.Extension
variable {n : Nat} {head tail : List (Event n)} {w : Nat} {thread : Fin n} {access : Access}

theorem run_append_code (run : Runs cfg code start events final) (suffix : List Instr) :
    Runs cfg (code++suffix) start events final := by
  induction run with
  | nil => exact .nil
  | cons step tail ih =>
    obtain ⟨fresh,i,fetch,dispatch⟩ := step
    have bound := (List.getElem?_eq_some_iff.mp fetch).1
    exact .cons ⟨fresh,i,by simpa [List.getElem?_append_left bound] using fetch,dispatch⟩ ih

/-- A suffix without stores cannot add a new memory source. -/
def ReadOnly (events : List (Event n)) : Prop :=
  ∀ thread access, Event.data thread access∈events → access.data.store=false

theorem prefix_store (readonly : ReadOnly tail)
    (observed : (head++tail)[w]?=some (.data thread access)) (store : access.data.store=true) :
    head[w]?=some (.data thread access) := by
  by_cases bound : w<head.length
  · simpa [List.getElem?_append_left bound] using observed
  · have h : tail[w-head.length]?=some (.data thread access) := by
      simpa [List.getElem?_append_right (by omega : head.length≤w)] using observed
    have := readonly thread access (List.mem_of_getElem? h)
    simp [store] at this

theorem compatible_prefix (compatible : Visibility.Compatible initial (head++tail) source)
    (readonly : ReadOnly tail) : Visibility.Compatible initial head source := by
  intro r reader ra observed read k
  have lifted : (head++tail)[r]?=some (.data reader ra) := by
    simpa [List.getElem?_append_left (List.getElem?_eq_some_iff.mp observed).1] using observed
  have h := compatible r reader ra lifted read k
  cases hs : source r k with
  | initial => simpa [hs] using h
  | store w j =>
    simp only [hs] at h
    obtain ⟨writer,wa,hw,store,space,address,value⟩ := h
    exact ⟨writer,wa,prefix_store readonly hw store,store,space,address,value⟩

theorem performed_prefix (performed : Visibility.Performed (head++tail) source) :
    Visibility.Performed head source := by
  have lift {i : Nat} {e : Event n} (h : head[i]?=some e) : (head++tail)[i]?=some e := by
    simpa [List.getElem?_append_left (List.getElem?_eq_some_iff.mp h).1] using h
  intro w r writer reader wa ra hw hr store read sw sr across j k same
  apply performed w r writer reader wa ra (lift hw) (lift hr) store read sw sr ?_ j k same
  obtain ⟨writer,reader,wa,ra,key,a,c,hw,hr,ha,hc,hwa,hac,hcr⟩ := across
  exact ⟨writer,reader,wa,ra,key,a,c,lift hw,lift hr,lift ha,lift hc,hwa,hac,hcr⟩

theorem view_append (readonly : ReadOnly tail) :
    CellMiddle.WordView.memory initial (head++tail) base width=CellMiddle.WordView.memory initial head base width := by
  have none (address : Nat) : tail.find? (CellMiddle.WordView.writesAt address)=none := by
    apply List.find?_eq_none.mpr
    intro event member
    cases event with
    | barrier => simp [CellMiddle.WordView.writesAt]
    | data thread access => simp [CellMiddle.WordView.writesAt,readonly thread access member]
  funext sp address
  cases sp <;> simp [CellMiddle.WordView.memory,CellMiddle.WordView.stored,List.find?_append,none]

end PtxTorchLean.Poisson.PTX.Concurrent.Extension

import PoissonPTX.ZeroSources

namespace PtxTorchLean.Poisson.PTX.Concurrent.WordSourceCheck

/-- Expected whole word for the first matching actual store, or initialization
when no matching store exists. Used only to construct/check finite witnesses. -/
def expected (initial : Space → Memory) (events : List (Event n)) (space : Space) (address : Nat) : Word :=
  let w := events.findIdx (ZeroSources.writes space address)
  if h : w<events.length then
    match events[w] with
    | .data _ access => access.data.value
    | .barrier _ => 0
  else read64 (initial space) address

/-- Each read is compared once as a whole word. Byte-level soundness is proved
below; performed-write constraints remain a separate obligation. -/
def check (initial : Space → Memory) (events : List (Event n)) : Bool :=
  events.all fun event => match event with
    | .data _ access => access.data.store ||
        access.data.value==expected initial events access.space access.data.address
    | .barrier _ => true

theorem sound (checked : check initial events=true) :
    Visibility.Compatible initial events (ZeroSources.source events) := by
  intro r reader ra observed read k
  have equal := List.all_eq_true.mp checked (.data reader ra) (List.mem_of_getElem? observed)
  have value : ra.data.value=expected initial events ra.space ra.data.address := by
    simpa [read] using equal
  simp only [ZeroSources.source,observed]
  by_cases found : events.findIdx (ZeroSources.writes ra.space ra.data.address)<events.length
  · simp only [found,ite_true]
    let w := events.findIdx (ZeroSources.writes ra.space ra.data.address)
    have yes := List.findIdx_getElem (p:=ZeroSources.writes ra.space ra.data.address) (xs:=events) (w:=found)
    have fetched : events[w]?=some events[w] := List.getElem?_eq_some_iff.mpr ⟨found,rfl⟩
    cases he : events[w] with
    | barrier => simp [w,he,ZeroSources.writes] at yes
    | data writer wa =>
      have props : (wa.data.store=true ∧ wa.space=ra.space) ∧ wa.data.address=ra.data.address := by
        simpa [← show w=events.findIdx (ZeroSources.writes ra.space ra.data.address) from rfl,he,ZeroSources.writes] using yes
      have observedW : events[w]?=some (.data writer wa) := by simpa [he] using fetched
      have words : ra.data.value=wa.data.value := by simpa [expected,found,← show w=events.findIdx (ZeroSources.writes ra.space ra.data.address) from rfl,he,show w<events.length from found] using value
      exact ⟨writer,wa,observedW,props.1.1,props.1.2,by rw [props.2],by rw [words]⟩
  · simp only [found,ite_false]
    have words : ra.data.value=read64 (initial ra.space) ra.data.address := by simpa [expected,found] using value
    rw [words]
    exact Sources.byte_read64 _ _ _

end PtxTorchLean.Poisson.PTX.Concurrent.WordSourceCheck

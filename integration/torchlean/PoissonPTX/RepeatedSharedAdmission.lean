import PoissonPTX.RepeatedShared

/-! Construct a necessary source-admission witness from actual preceding
producers. Chronological coherence is used only as an existence witness. -/
namespace PtxTorchLean.Poisson.PTX.Concurrent.Visibility.Repeated

/-- The chosen store provides the word and surrounds every other overlapping
writer causally. In particular it occurs before the read. -/
def Producer (events : List (Event n)) (r : Nat) (ra : Access) (w : Nat) : Prop :=
  ∃ writer wa, events[w]?=some (.data writer wa) ∧ wa.data.store=true ∧
    wa.space=.shared ∧ ra.space=.shared ∧ wa.data.address=ra.data.address ∧
    wa.data.value=ra.data.value ∧ w<r ∧ WritersAround events w r ra.data.address

/-- Supply explicit byte sources and necessary ordering from established
producer facts. The theorem does not assume that proposed reads are correct. -/
theorem construct_sources (events : List (Event n))
    (producers : ∀ r reader ra, events[r]?=some (.data reader ra) → ra.data.store=false →
      ∃ w, Producer events r ra w) :
    ∃ source, Compatible initial events source ∧ OrderedSources events source := by
  classical
  have choices : ∀ r, ∃ w, ∀ reader ra, events[r]?=some (.data reader ra) → ra.data.store=false →
      Producer events r ra w := by
    intro r
    cases found : events[r]? with
    | none => exact ⟨0,by intro reader ra h; simp at h⟩
    | some event =>
      cases event with
      | barrier b => exact ⟨0,by intro reader ra h; simp at h⟩
      | data reader ra =>
        by_cases read : ra.data.store=false
        · obtain ⟨w,hw⟩ := producers r reader ra found read
          refine ⟨w,?_⟩
          intro other a atR isRead
          have eq := Option.some.inj atR
          cases eq
          exact hw
        · exact ⟨0,by intro other a atR isRead; have eq := Option.some.inj atR; cases eq; contradiction⟩
  choose selected spec using choices
  let source : Nat → Fin 8 → Sources.Origin Nat := fun r k => .store (selected r) k
  refine ⟨source,?_,?_⟩
  · intro r reader ra found read k
    obtain ⟨writer,wa,hw,write,sw,sr,address,value,before,around⟩ := spec r reader ra found read
    exact ⟨writer,wa,hw,write,sw.trans sr.symm,by rw [address],by rw [value]⟩
  · refine ⟨Nat.lt,?_,?_,?_⟩
    · intro a b left right la ra ha hb wl wr sl sr order j k same
      exact before_lt order
    · intro r w reader writer ra wa hr hw read write sr sw order j k same
      obtain ⟨owner,sa,hs,ws,ss,rs,addr,value,before,around⟩ := spec r reader ra hr read
      intro eq
      have selectedEq : selected r=w := by cases eq; rfl
      have later := before_lt order
      omega
    · intro w r writer reader wa ra hw hr write read sw sr order j k same
      obtain ⟨owner,sa,hs,ws,ss,rs,addr,value,before,around⟩ := spec r reader ra hr read
      change ¬selected r<w
      have earlier := before_lt order
      rcases around w writer wa hw write sw j k same with eq | past | future
      · omega
      · have prior := before_lt past; omega
      · have after := before_lt future; omega

end PtxTorchLean.Poisson.PTX.Concurrent.Visibility.Repeated

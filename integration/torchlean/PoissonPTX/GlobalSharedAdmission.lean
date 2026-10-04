import PoissonPTX.RepeatedSharedAdmission

namespace PtxTorchLean.Poisson.PTX.Concurrent.Visibility.Repeated

/-- Join immutable global input reads and causally published shared reads.
Coherence is chosen chronologically only for this existence witness; the
producer obligations still demand the actual causal writer relationships. -/
theorem construct_global_shared (events : List (Event n))
    (globals : ∀ (r : Nat) (reader : Fin n) (ra : Access), events[r]?=some (.data reader ra) → ra.data.store=false →
      ra.space=.global → ra.data.value=read64 (initial .global) ra.data.address)
    (producers : ∀ (r : Nat) (reader : Fin n) (ra : Access), events[r]?=some (.data reader ra) → ra.data.store=false →
      ra.space=.shared → ∃ w, Producer events r ra w) :
    ∃ source, Compatible initial events source ∧ OrderedSources events source := by
  classical
  have choices : ∀ r, ∃ w, ∀ reader ra, events[r]?=some (.data reader ra) → ra.data.store=false →
      ra.space=.shared → Producer events r ra w := by
    intro r
    cases found : events[r]? with
    | none => exact ⟨0,by intro reader ra h; simp at h⟩
    | some event =>
      cases event with
      | barrier b => exact ⟨0,by intro reader ra h; simp at h⟩
      | data reader ra =>
        by_cases read : ra.data.store=false ∧ ra.space=.shared
        · obtain ⟨w,hw⟩ := producers r reader ra found read.1 read.2
          refine ⟨w,?_⟩
          intro other a atR isRead shared
          have eq := Option.some.inj atR
          cases eq
          exact hw
        · exact ⟨0,by intro other a atR isRead shared; have eq := Option.some.inj atR; cases eq; exact False.elim (read ⟨isRead,shared⟩)⟩
  choose selected spec using choices
  let isShared : Nat → Bool := fun r => match events[r]? with
    | some (.data _ a) => a.space==.shared
    | _ => false
  let source : Nat → Fin 8 → Sources.Origin Nat := fun r k =>
    if isShared r then .store (selected r) k else .initial
  have chosen : ∀ (r : Nat) (reader : Fin n) (ra : Access), events[r]?=some (.data reader ra) → ra.space=.shared →
      ∀ k, source r k=.store (selected r) k := by
    intro r reader ra found shared k; simp [source,isShared,found,shared]
  refine ⟨source,?_,?_⟩
  · intro r reader ra found read k
    cases space : ra.space with
    | global =>
      have value := globals r reader ra found read space
      simp [source,isShared,found,space,value,Sources.byte_read64]
    | shared =>
      rw [chosen r reader ra found space k]
      obtain ⟨writer,wa,hw,write,sw,sr,address,value,before,around⟩ := spec r reader ra found read space
      exact ⟨writer,wa,hw,write,sw,by rw [address],by rw [value]⟩
  · refine ⟨Nat.lt,?_,?_,?_⟩
    · intro a b left right la ra ha hb wl wr sl sr order j k same
      exact before_lt order
    · intro r w reader writer ra wa hr hw read write sr sw order j k same
      obtain ⟨owner,sa,hs,ws,ss,rs,addr,value,before,around⟩ := spec r reader ra hr read sr
      rw [chosen r reader ra hr sr k]
      intro eq
      have selectedEq : selected r=w := by cases eq; rfl
      have later := before_lt order
      omega
    · intro w r writer reader wa ra hw hr write read sw sr order j k same
      obtain ⟨owner,sa,hs,ws,ss,rs,addr,value,before,around⟩ := spec r reader ra hr read sr
      rw [chosen r reader ra hr sr k]
      change ¬selected r<w
      have earlier := before_lt order
      rcases around w writer wa hw write sw j k same with eq | past | future
      · omega
      · have prior := before_lt past; omega
      · have after := before_lt future; omega

end PtxTorchLean.Poisson.PTX.Concurrent.Visibility.Repeated

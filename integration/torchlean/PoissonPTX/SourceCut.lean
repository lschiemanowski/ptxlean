import PoissonPTX.BarrierSources

namespace PtxTorchLean.Poisson.PTX.Concurrent.SourceCut
open Ptx
variable {n : Nat} {before after : List (Event n)}

/-- A byte supplied by some actual store in the discarded prefix. -/
def Covered (events : List (Event n)) (space : Space) (address : Nat) : Prop :=
  ∃ writer access, Event.data writer access∈events ∧ access.data.store=true ∧
    access.space=space ∧ ∃ j : Fin 8, access.data.address+j.val=address

/-- An accounting view of actual prefix stores. This does not update any lane
state or grant visibility: compatibility is proved separately from real order. -/
structure Published (initial snapshot : Space → Memory) (events : List (Event n)) : Prop where
  stored : ∀ writer access, Event.data writer access∈events → access.data.store=true →
    ∀ j : Fin 8, snapshot access.space (access.data.address+j.val)=byte access.data.value j.val
  outside : ∀ space address, ¬Covered events space address → snapshot space address=initial space address

/-- Removing a performed prefix converts its store origins to initialization;
all retained store origins keep their byte offset and shift by the cut length. -/
def source (cut : Nat) (original : Nat → Fin 8 → Sources.Origin Nat)
    (r : Nat) (k : Fin 8) : Sources.Origin Nat :=
  match original (cut+r) k with
  | .initial => .initial
  | .store w j => if w<cut then .initial else .store (w-cut) j

/-- No store value or read value is assumed by this ordering condition. -/
def Ordered (events : List (Event n)) : Prop :=
  ∃ c key, events[c]?=some (.barrier (.completion key)) ∧
    ∀ (w : Nat) writer access, events[w]?=some (.data writer access) → access.data.store=true →
      access.space=.shared ∧ ∃ a, events[a]?=some (.barrier (.arrival key writer)) ∧ w<a ∧ a<c

/-- Actual stores in the two segments touch disjoint bytes of the same space. -/
def Separate (before after : List (Event n)) : Prop :=
  ∀ writer wa, Event.data writer wa∈before → wa.data.store=true →
    ∀ other wb, Event.data other wb∈after → wb.data.store=true → wa.space=wb.space →
      ∀ j k : Fin 8, wa.data.address+j.val≠wb.data.address+k.val

theorem left {r : Nat} {event : Event n} (h : before[r]?=some event) :
    (before++after)[r]?=some event := by
  simpa only [List.getElem?_append_left (List.getElem?_eq_some_iff.mp h).1] using h

theorem right {r : Nat} {event : Event n} (h : after[r]?=some event) :
    (before++after)[before.length+r]?=some event := by
  simpa only [List.getElem?_append_right (Nat.le_add_right _ _),Nat.add_sub_cancel_left] using h

/-- Any store in the prefix is before a later read through the real barrier. -/
theorem across (ordered : Ordered before) {w r : Nat}
    (hw : before[w]?=some (.data writer wa)) (write : wa.data.store=true)
    (hr : after[r]?=some (.data reader ra)) : Visibility.Across (before++after) w (before.length+r) := by
  obtain ⟨c,key,hc,stores⟩ := ordered
  obtain ⟨shared,a,ha,hwa,hac⟩ := stores w writer wa hw write
  have bound := (List.getElem?_eq_some_iff.mp hc).1
  exact ⟨writer,reader,wa,ra,key,a,c,left hw,right hr,left ha,left hc,hwa,hac,by omega⟩

/-- A source still naming initialization cannot refer to a byte changed by an
ordered prefix write. This holds per byte, including partially overlapping reads. -/
theorem initial_unchanged (ordered : Ordered before)
    (performed : Visibility.Performed (before++after) original)
    {r : Nat} (hr : after[r]?=some (.data reader ra)) (read : ra.data.store=false)
    (k : Fin 8) (chosen : original (before.length+r) k=.initial) :
    ¬Covered before ra.space (ra.data.address+k.val) := by
  rintro ⟨writer,wa,member,write,space,j,address⟩
  obtain ⟨w,hw⟩ := List.mem_iff_getElem?.mp member
  have shared := (ordered.choose_spec.choose_spec.2 w writer wa hw write).1
  exact performed w (before.length+r) writer reader wa ra (left hw) (right hr)
    write read shared (space.symm.trans shared) (across ordered hw write hr) j k address chosen

/-- Rebase a continuation's source account to a proved prefix publication.
The candidate execution itself and all its registers/memories are unchanged. -/
theorem compatible (publication : Published initial snapshot before) (ordered : Ordered before)
    (whole : Visibility.Compatible initial (before++after) original)
    (performed : Visibility.Performed (before++after) original) :
    Visibility.Compatible snapshot after (source before.length original) := by
  intro r reader ra hr read k
  have h := whole (before.length+r) reader ra (right hr) read k
  cases hs : original (before.length+r) k with
  | initial =>
    simp only [source,hs]
    rw [publication.outside _ _ (initial_unchanged ordered performed hr read k hs)]
    simpa only [hs] using h
  | store w j =>
    simp only [hs] at h
    obtain ⟨writer,wa,hw,write,space,address,value⟩ := h
    by_cases early : w<before.length
    · have beforeStore : before[w]?=some (.data writer wa) := by
        simpa only [List.getElem?_append_left early] using hw
      simp only [source,hs,early,↓reduceIte]
      rw [←space,←address,publication.stored writer wa (List.mem_of_getElem? beforeStore) write j]
      exact value
    · have afterStore : after[w-before.length]?=some (.data writer wa) := by
        simpa only [List.getElem?_append_right (Nat.le_of_not_gt early)] using hw
      simp only [source,hs,early,↓reduceIte]
      exact ⟨writer,wa,afterStore,write,space,address,value⟩

/-- A continuation barrier order remains a barrier order in the joint history. -/
theorem across_right (h : Visibility.Across after w r) :
    Visibility.Across (before++after) (before.length+w) (before.length+r) := by
  obtain ⟨writer,reader,wa,ra,key,a,c,hw,hr,ha,hc,hwa,hac,hcr⟩ := h
  exact ⟨writer,reader,wa,ra,key,before.length+a,before.length+c,
    right hw,right hr,right ha,right hc,by omega,by omega,by omega⟩

/-- Later performed writes cannot be mistaken for rebased initialization.
The disjointness condition prevents an earlier prefix store from covering the
same byte as a continuation producer. -/
theorem performed (separate : Separate before after)
    (whole : Visibility.Compatible initial (before++after) original)
    (performs : Visibility.Performed (before++after) original) :
    Visibility.Performed after (source before.length original) := by
  intro w r writer reader wa ra hw hr write read sw sr order j k address
  have noninitial := performs (before.length+w) (before.length+r) writer reader wa ra
    (right hw) (right hr) write read sw sr (across_right order) j k address
  intro initial
  cases hs : original (before.length+r) k with
  | initial => exact noninitial hs
  | store old off =>
    by_cases early : old<before.length
    · have comp := whole (before.length+r) reader ra (right hr) read k
      simp only [hs] at comp
      obtain ⟨previous,a,ha,store,space,same,bytes⟩ := comp
      have atBefore : before[old]?=some (.data previous a) := by
        simpa only [List.getElem?_append_left early] using ha
      exact separate previous a (List.mem_of_getElem? atBefore) store writer wa (List.mem_of_getElem? hw)
        write (space.trans (sr.trans sw.symm)) off j (same.trans address.symm)
    · simp [source,hs,early] at initial

end PtxTorchLean.Poisson.PTX.Concurrent.SourceCut

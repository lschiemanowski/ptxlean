import PoissonPTX.BarrierSources
import Ptx.Memory

namespace PtxTorchLean.Poisson.PTX.Concurrent.Visibility.Repeated

/-- Same-thread memory accesses follow the order of their actual occurrences.
Different threads obtain no order merely from their positions in this list. -/
def ThreadBefore (events : List (Event n)) (a b : Nat) : Prop :=
  ∃ thread left right, events[a]?=some (.data thread left) ∧
    events[b]?=some (.data thread right) ∧ a<b

/-- The barrier edge refers to real arrival/completion records, just as Across.
Using it for PTX interpretation requires a fetched run and its barrier history. -/
def Edge (events : List (Event n)) (a b : Nat) : Prop :=
  ThreadBefore events a b ∨ Across events a b

def Before (events : List (Event n)) : Nat → Nat → Prop := Ptx.Path (Edge events)

theorem before_lt (ordered : Before events a b) : a<b := by
  apply Ptx.Path.rank_increases id _ ordered
  intro a b edge
  change a<b
  rcases edge with ⟨thread,left,right,ha,hb,lt⟩ | ⟨writer,reader,wa,ra,key,x,y,hw,hr,hx,hy,one,two,three⟩
  · exact lt
  · omega

/-- Necessary constraints from PTX 9.4 §§8.10.1 and 8.10.6, restricted to
same-CTA synchronous shared accesses with identity addresses and generic proxy.
Coherence is supplied explicitly, not equated with scheduling order. This is
not full PTX admission; in particular dependent no-thin-air remains separate. -/
structure OrderedSources (events : List (Event n)) (source : Nat → Fin 8 → Sources.Origin Nat) : Prop where
  ordered : ∃ coherence : Nat → Nat → Prop,
    (∀ a b left right la ra, events[a]?=some (.data left la) → events[b]?=some (.data right ra) →
      la.data.store=true → ra.data.store=true → la.space=.shared → ra.space=.shared →
      Before events a b → ∀ j k : Fin 8, la.data.address+j.val=ra.data.address+k.val → coherence a b) ∧
    (∀ r w reader writer ra wa, events[r]?=some (.data reader ra) → events[w]?=some (.data writer wa) →
      ra.data.store=false → wa.data.store=true → ra.space=.shared → wa.space=.shared →
      Before events r w → ∀ j k : Fin 8, wa.data.address+j.val=ra.data.address+k.val → source r k≠.store w j) ∧
    (∀ w r writer reader wa ra, events[w]?=some (.data writer wa) → events[r]?=some (.data reader ra) →
      wa.data.store=true → ra.data.store=false → wa.space=.shared → ra.space=.shared →
      Before events w r → ∀ j k : Fin 8, wa.data.address+j.val=ra.data.address+k.val →
      match source r k with | .initial => False | .store old _ => ¬coherence old w)

/-- The older performed-write condition is a consequence, so existing
single-writer cell theorems remain usable without modifying their contracts. -/
theorem OrderedSources.performed (h : OrderedSources events source) : Performed events source := by
  obtain ⟨coherence,ordered,future,stale⟩ := h.ordered
  intro w r writer reader wa ra hw hr store read ws rs across j k address chosen
  have noOld := stale w r writer reader wa ra hw hr store read ws rs (.edge (.inr across)) j k address
  simpa [chosen] using noOld

/-- Every other writer of a read byte belongs strictly before the selected
stage write or strictly after the read. This is a history/ownership condition,
not a claim about any register, read result, sum or source assignment. -/
def WritersAround (events : List (Event n)) (w r address : Nat) : Prop :=
  ∀ other thread access, events[other]?=some (.data thread access) →
    access.data.store=true → access.space=.shared → ∀ j k : Fin 8,
    access.data.address+j.val=address+k.val →
    other=w ∨ Before events other w ∨ Before events r other

/-- Freshness follows byte by byte from actual writer positions and the
necessary ordering constraints. Source uniformity is a conclusion. -/
theorem read_from_stage (compatible : Compatible initial events source)
    (admitted : OrderedSources events source)
    (hw : events[w]?=some (.data writer wa)) (hr : events[r]?=some (.data reader ra))
    (write : wa.data.store=true) (read : ra.data.store=false)
    (sw : wa.space=.shared) (sr : ra.space=.shared)
    (same : wa.data.address=ra.data.address) (before : Before events w r)
    (around : WritersAround events w r ra.data.address) :
    ra.data.value=wa.data.value ∧ ∀ k, source r k=.store w k := by
  obtain ⟨coherence,ordered,future,stale⟩ := admitted.ordered
  have chosen : ∀ k, source r k=.store w k ∧ byte ra.data.value k.val=byte wa.data.value k.val := by
    intro k
    have h := compatible r reader ra hr read k
    have recent := stale w r writer reader wa ra hw hr write read sw sr before k k (by rw [same])
    cases hs : source r k with
    | initial => simpa [hs] using recent
    | store other j =>
      simp only [hs] at h recent
      obtain ⟨thread,access,found,store,space,address,value⟩ := h
      have shared := space.trans sr
      rcases around other thread access found store shared j k address with own | earlier | later
      · subst other
        have eq : access=wa := by have e := Option.some.inj (found.symm.trans hw); cases e; rfl
        subst access
        have jk : j=k := by apply Fin.ext; omega
        subst j
        exact ⟨rfl,value⟩
      · exact False.elim (recent (ordered other w thread writer access wa found hw store write shared sw earlier
          j k (by simpa [same] using address)))
      · exact False.elim (future r other reader thread ra access hr found read store sr shared later j k address hs)
  exact ⟨Sources.word_eq_of_bytes _ _ (fun k => (chosen k).2),fun k => (chosen k).1⟩

end PtxTorchLean.Poisson.PTX.Concurrent.Visibility.Repeated

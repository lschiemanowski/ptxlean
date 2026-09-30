import PoissonPTX.ConcurrentExtension

namespace PtxTorchLean.Poisson.PTX.Concurrent.Projection
variable {n : Nat} {small large : List (Event n)}

/-- Retain events in their original order. Positions, not event equality, identify
sources: two equal-looking stores are still distinct occurrences. -/
structure Embedding (small large : List (Event n)) where
  position : Nat → Nat
  increasing : StrictMono position
  fetch : ∀ r, r<small.length → large[position r]?=small[r]?

def Retained (embedding : Embedding small large) (w : Nat) : Prop :=
  ∃ v, v<small.length ∧ embedding.position v=w

/-- An omitted store cannot cover any byte of a retained read in the same space.
This is a geometric condition, independent of stored or loaded values. -/
def Separated (embedding : Embedding small large) : Prop :=
  ∀ (w : Nat) (writer : Fin n) (wa : Access), large[w]?=some (.data writer wa) → wa.data.store=true →
    ¬Retained embedding w → ∀ (r : Nat) (reader : Fin n) (ra : Access), small[r]?=some (.data reader ra) →
    ra.data.store=false → wa.space=ra.space →
    ∀ j k : Fin 8, wa.data.address+j.val≠ra.data.address+k.val

noncomputable def source (embedding : Embedding small large)
    (original : Nat → Fin 8 → Sources.Origin Nat) (r : Nat) (k : Fin 8) : Sources.Origin Nat :=
  match original (embedding.position r) k with
  | .initial => .initial
  | .store w j => .store (Function.invFun embedding.position w) j

theorem observed (embedding : Embedding small large) (h : small[r]?=some event) :
    large[embedding.position r]?=some event := by
  rw [embedding.fetch r (List.getElem?_eq_some_iff.mp h).1,h]

/-- Restriction preserves each chosen byte source, with store positions renamed.
It does not substitute a different memory account for the retained execution. -/
theorem compatible (embedding : Embedding small large) (separated : Separated embedding)
    (whole : Visibility.Compatible initial large original) :
    Visibility.Compatible initial small (source embedding original) := by
  intro r reader ra readAt read k
  have h := whole _ reader ra (observed embedding readAt) read k
  cases hs : original (embedding.position r) k with
  | initial => simpa [source,hs] using h
  | store w j =>
    simp only [hs] at h
    obtain ⟨writer,wa,writeAt,write,space,address,value⟩ := h
    have kept : Retained embedding w := by
      by_contra omitted
      exact separated w writer wa writeAt write omitted r reader ra readAt read space j k address
    obtain ⟨v,bound,position⟩ := kept
    have inverse : Function.invFun embedding.position w=v := by
      rw [← position]
      exact Function.leftInverse_invFun embedding.increasing.injective v
    have atV : small[v]?=some (.data writer wa) := by
      rw [← embedding.fetch v bound,position,writeAt]
    simp only [source,hs,inverse]
    exact ⟨writer,wa,atV,write,space,address,value⟩


/-- Actual arrival/completion order survives the strictly increasing embedding. -/
theorem across (embedding : Embedding small large) (h : Visibility.Across small w r) :
    Visibility.Across large (embedding.position w) (embedding.position r) := by
  obtain ⟨writer,reader,wa,ra,key,a,c,hw,hr,ha,hc,waLt,acLt,crLt⟩ := h
  exact ⟨writer,reader,wa,ra,key,embedding.position a,embedding.position c,
    observed embedding hw,observed embedding hr,observed embedding ha,observed embedding hc,
    embedding.increasing waLt,embedding.increasing acLt,embedding.increasing crLt⟩

theorem performed (embedding : Embedding small large)
    (whole : Visibility.Performed large original) : Visibility.Performed small (source embedding original) := by
  intro w r writer reader wa ra hw hr write read sw sr order j k same
  have h := whole _ _ writer reader wa ra (observed embedding hw) (observed embedding hr)
    write read sw sr (across embedding order) j k same
  cases hs : original (embedding.position r) k with
  | initial => exact False.elim (h hs)
  | store v b => simp [source,hs]

/-- A layout fence is an exclusive upper bound for every retained global read
and a lower bound for every omitted global store. Shared accesses are separate. -/
theorem separated_by_fence (embedding : Embedding small large)
    (reads : ∀ (r : Nat) (reader : Fin n) (ra : Access), small[r]?=some (.data reader ra) → ra.data.store=false →
      ra.space=.global → ra.data.address+8≤fence)
    (writes : ∀ (w : Nat) (writer : Fin n) (wa : Access), large[w]?=some (.data writer wa) → wa.data.store=true →
      ¬Retained embedding w → wa.space=.global ∧ fence≤wa.data.address) : Separated embedding := by
  intro w writer wa hw write omitted r reader ra hr read space j k same
  obtain ⟨global,lower⟩ := writes w writer wa hw write omitted
  have upper := reads r reader ra hr read (space.symm.trans global)
  have hj := j.isLt; have hk := k.isLt
  omega

end PtxTorchLean.Poisson.PTX.Concurrent.Projection

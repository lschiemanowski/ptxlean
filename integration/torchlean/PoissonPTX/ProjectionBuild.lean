import PoissonPTX.ConcurrentProjection

namespace PtxTorchLean.Poisson.PTX.Concurrent.Projection
variable {n : Nat} {small large : List (Event n)}

def empty (large : List (Event n)) : Embedding [] large where
  position := id
  increasing := fun _ _ h => h
  fetch := by simp

/-- Drop a step's events while keeping occurrence identities in the rest. -/
def drop (embedding : Embedding small large) (chunk : List (Event n)) : Embedding small (chunk++large) where
  position := fun r => chunk.length+embedding.position r
  increasing := by intro a b h; dsimp only; have := embedding.increasing h; omega
  fetch := by
    intro r hr
    rw [List.getElem?_append_right (by omega)]
    simpa using embedding.fetch r hr

/-- Keep all events emitted by a projected step, then use the rest's embedding. -/
def keep (embedding : Embedding small large) (chunk : List (Event n)) : Embedding (chunk++small) (chunk++large) where
  position := fun r => if r<chunk.length then r else chunk.length+embedding.position (r-chunk.length)
  increasing := by
    intro a b h
    dsimp only
    split <;> split
    · exact h
    · omega
    · omega
    · have := embedding.increasing (show a-chunk.length<b-chunk.length by omega); omega
  fetch := by
    intro r hr
    split
    · rw [List.getElem?_append_left ‹_›,List.getElem?_append_left ‹_›]
    · rw [List.getElem?_append_right (by omega),List.getElem?_append_right (by omega)]
      simpa using embedding.fetch (r-chunk.length) (by simp only [List.length_append] at hr; omega)


/-- A property of every omitted occurrence, not merely of its event value. -/
def Omitted (P : Event n → Prop) (embedding : Embedding small large) : Prop :=
  ∀ w e, large[w]?=some e → ¬Retained embedding w → P e

theorem omitted_keep (h : Omitted P embedding) :
    Omitted P (keep embedding chunk) := by
  intro w e fetch omitted
  by_cases before : w<chunk.length
  · exfalso; apply omitted
    exact ⟨w,by simp only [List.length_append]; omega,by simp [keep,before]⟩
  · rw [List.getElem?_append_right (by omega)] at fetch
    apply h (w-chunk.length) e fetch
    intro retained
    obtain ⟨v,bound,position⟩ := retained
    apply omitted
    refine ⟨chunk.length+v,by simp only [List.length_append]; omega,?_⟩
    simp only [keep]
    rw [ite_eq_right (by omega),Nat.add_sub_cancel_left,position]
    omega

theorem omitted_drop (h : Omitted P embedding) (all : ∀ e∈chunk, P e) :
    Omitted P (drop embedding chunk) := by
  intro w e fetch omitted
  by_cases before : w<chunk.length
  · rw [List.getElem?_append_left before] at fetch
    exact all e (List.mem_of_getElem? fetch)
  · rw [List.getElem?_append_right (by omega)] at fetch
    apply h (w-chunk.length) e fetch
    intro retained
    obtain ⟨v,bound,position⟩ := retained
    apply omitted
    exact ⟨v,bound,by dsimp [drop]; rw [position]; omega⟩

end PtxTorchLean.Poisson.PTX.Concurrent.Projection

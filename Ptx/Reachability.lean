import Ptx.Memory

/-!
# Verified finite nonempty reachability

The vertex-elimination recurrence adds paths through one intermediate vertex at
a time. Its base is the supplied edge relation, not the identity relation:
diagonal entries become true exactly when a nonempty cycle exists. The proof
does not assume acyclicity, distinct list entries, or a bound on path length.
-/

namespace Ptx

/-- Floyd–Warshall recurrence for a supplied list of intermediate vertices.
This simple functional version does not claim a memoized cubic implementation. -/
def reachableVia (r : α → α → Bool) : List α → α → α → Bool
  | [] => r
  | vertex :: rest => fun a b =>
      reachableVia r rest a b ||
        (reachableVia r rest a vertex && reachableVia r rest vertex b)

theorem reachableVia_edge (vertices : List α) (edge : r a b = true) :
    reachableVia r vertices a b = true := by
  induction vertices with
  | nil => exact edge
  | cons vertex rest ih => simp only [reachableVia, ih, Bool.true_or]

theorem reachableVia_sound (vertices : List α)
    (h : reachableVia r vertices a b = true) :
    Path (fun x y => r x y = true) a b := by
  induction vertices generalizing a b with
  | nil => exact .edge h
  | cons vertex rest ih =>
      simp only [reachableVia, Bool.or_eq_true, Bool.and_eq_true] at h
      rcases h with direct | ⟨first, second⟩
      · exact ih direct
      · exact .join (ih first) (ih second)

/-- The resulting relation composes at every processed intermediate vertex. -/
theorem reachableVia_trans (vertices : List α) (middle : b ∈ vertices)
    (first : reachableVia r vertices a b = true)
    (second : reachableVia r vertices b c = true) :
    reachableVia r vertices a c = true := by
  induction vertices generalizing a b c with
  | nil => simp at middle
  | cons vertex rest ih =>
      simp only [reachableVia, Bool.or_eq_true, Bool.and_eq_true] at first second ⊢
      rcases List.mem_cons.mp middle with rfl | middle
      · rcases first with direct₁ | ⟨headPath, _⟩ <;>
          rcases second with direct₂ | ⟨_, tailPath⟩
        · exact Or.inr ⟨direct₁, direct₂⟩
        · exact Or.inr ⟨direct₁, tailPath⟩
        · exact Or.inr ⟨headPath, direct₂⟩
        · exact Or.inr ⟨headPath, tailPath⟩
      · rcases first with direct₁ | ⟨headPath, via₁⟩ <;>
          rcases second with direct₂ | ⟨via₂, tailPath⟩
        · exact Or.inl (ih middle direct₁ direct₂)
        · exact Or.inr ⟨ih middle direct₁ via₂, tailPath⟩
        · exact Or.inr ⟨headPath, ih middle via₁ direct₂⟩
        · exact Or.inr ⟨headPath, tailPath⟩

/-- Decide nonempty directed reachability, including reachability from a vertex to itself. -/
def reachable (r : Fin n → Fin n → Bool) (a b : Fin n) : Bool :=
  reachableVia r (List.ofFn (fun vertex : Fin n => vertex)) a b

theorem reachable_iff (r : Fin n → Fin n → Bool) (a b : Fin n) :
    reachable r a b = true ↔ Path (fun x y => r x y = true) a b := by
  constructor
  · exact reachableVia_sound _
  · intro path
    induction path with
    | edge edge => exact reachableVia_edge _ edge
    | @join a middle b first second ih₁ ih₂ =>
        apply reachableVia_trans _ _ ih₁ ih₂
        exact List.mem_ofFn.mpr ⟨middle, rfl⟩

end Ptx

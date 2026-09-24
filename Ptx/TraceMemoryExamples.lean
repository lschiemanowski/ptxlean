import Ptx.TraceMemory
import Ptx.GraphTransport

/-! Distinguishing structural checks: repeated PCs, gaps and mixed storage spaces.
These records test the projection, not a claim that an arbitrary trace executed. -/
namespace Ptx.TraceMemory.Examples

private def load : Access 2 := ⟨⟨0,0⟩,.load .relaxed,7⟩
private def memory (pc : Nat) : Option (Access 2) := if pc = 9 then some load else none

example : (project memory [9,4,9]).map Projected.position = [0,2] := by decide
example : (project memory [9,4,9]).map Projected.origin = [9,9] := by decide

private def catalogue : Catalogue 2 :=
  ⟨fun i => if i.val = 0 then .global 0 else .shared 0 0 0 0 0,
   by intro a b h; have ha := a.isLt; have hb := b.isLt
      by_cases a.val = 0 <;> by_cases b.val = 0 <;> simp_all <;> apply Fin.ext <;> omega⟩
private def globalWord : Location 2 := ⟨0,0⟩
private def sharedWord : Location 2 := ⟨1,0⟩
example : globalWord.code ≠ sharedWord.code := by decide
example : catalogue.key globalWord.storage ≠ catalogue.key sharedWord.storage := by decide

private def mixed : Graph 3 where
  event := fun i => ⟨some 0, i.val,
    ⟨.store .relaxed, if i.val = 1 then sharedWord.code else globalWord.code, 0⟩⟩
  source := id
  co := fun _ _ => false

-- Causality between global endpoints may pass through a shared-memory event.
example : mixed.cause 0 2 := by
  apply Or.inl
  refine ⟨Path.join (b := 1) (Path.edge (Or.inl ?_)) (Path.edge (Or.inl ?_)), ?_⟩
  · simp [Graph.po, mixed]
  · simp [Graph.po, mixed]
  · simp [Graph.sameAddress, mixed]
example : ¬ mixed.sameAddress 0 1 := by simp [Graph.sameAddress, mixed, globalWord, sharedWord, Location.code]

-- Renaming preserves the original memory obligations in both directions.
example (g : Graph n) : (GraphTransport.renameAddresses g (fun a => a + 17)).Valid ↔ g.Valid :=
  GraphTransport.renameAddresses_valid_iff g _ (fun _ _ h => by omega)

end Ptx.TraceMemory.Examples

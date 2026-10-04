import PoissonPTX.DotTreeReads
import PoissonPTX.ReductionWitnessWords

namespace PtxTorchLean.Poisson.PTX.Concurrent.Dot.Witness
open Reduction.Control.Witness256

/-- Exact words carried by the constructed trace, not an assumption in the
universal numerical theorem. Barrier records impose no numerical condition. -/
def Expected (input : Nat → Word) : Event 256 → Prop
  | .barrier _ => True
  | .data t a =>
    a.space=.shared ∧ a.data.pc<96 ∧
    (a.data.store=false → ∃ (k : Fin 8) (right : Bool), a.data.pc=readPC k right) ∧
    (∀ phase : Fin 9, a.data.pc=storeSite phase → a.data.value=words input phase.val t.val) ∧
    (∀ (k : Fin 8) (right : Bool), a.data.pc=readPC k right →
      a.data.value=words input k.val (t.val+(readOffset k right)))

theorem initial_expected (s : PTX.State) (thread : Fin 256)
    (pc : s.pc=20) (value : s.regs 8=input thread.val)
    (a : Access) (member : a∈initialEvents s) : Expected input (.data thread a) := by
  simp only [initialEvents,List.mem_singleton] at member
  subst a
  refine ⟨rfl, by simp only [pc]; omega, (by intro h; cases h), ?_, ?_⟩
  · intro phase atSite
    have zero : phase.val=0 := by simp only [pc,storeSite] at atSite; omega
    simpa only [zero,words] using value
  · intro k right atRead
    cases right <;> simp only [pc,readPC,Bool.false_eq_true,↓reduceIte] at atRead <;> omega

theorem update_expected (input : Nat → Word) (s : PTX.State) (k : Fin 8) (thread : Fin 256)
    (pc : s.pc=26+9*k.val) (live : thread.val<stride k)
    (a : Access) (member : a∈updateEvents s (Reduction.Control.readOffset k true)
      (words input k.val thread.val) (words input k.val (thread.val+stride k))) :
    Expected input (.data thread a) := by
  simp only [updateEvents,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl|rfl|rfl
  · refine ⟨rfl, by have := k.isLt; simp only [pc]; omega, by intro _; exact ⟨k,false,by simp [pc,readPC]; omega⟩, ?_, ?_⟩
    · intro phase atSite; simp only [pc,storeSite] at atSite; omega
    · intro q right atRead
      cases right
      · have eq : q.val=k.val := by simp only [pc,readPC,Bool.false_eq_true,↓reduceIte] at atRead; omega
        simp only [eq,readOffset,Bool.false_eq_true,↓reduceIte,Nat.add_zero]
      · simp only [pc,readPC,↓reduceIte] at atRead; omega
  · refine ⟨rfl, by have := k.isLt; simp only [pc]; omega, by intro _; exact ⟨k,true,by simp [pc,readPC]; omega⟩, ?_, ?_⟩
    · intro phase atSite; simp only [pc,storeSite] at atSite; omega
    · intro q right atRead
      cases right
      · simp only [pc,readPC,Bool.false_eq_true,↓reduceIte] at atRead; omega
      · have eq : q=k := by apply Fin.ext; simp only [pc,readPC,↓reduceIte] at atRead; omega
        subst q; rfl
  · refine ⟨rfl, by have := k.isLt; simp only [pc]; omega, (by intro h; cases h), ?_, ?_⟩
    · intro phase atSite
      have eq : phase.val=k.val+1 := by simp only [pc,storeSite] at atSite; omega
      rw [eq,words]
      simp only [show thread.val<256 / 2^(k.val+1) from live,↓reduceIte]
      rfl
    · intro q right atRead
      cases right <;> simp only [pc,readPC,Bool.false_eq_true,↓reduceIte] at atRead <;> omega


end PtxTorchLean.Poisson.PTX.Concurrent.Dot.Witness

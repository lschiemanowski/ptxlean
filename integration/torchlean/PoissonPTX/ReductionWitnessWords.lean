import PoissonPTX.ReductionLocal

namespace PtxTorchLean.Poisson.PTX.Concurrent.Reduction.Control.Witness256

/-- Canonical result words choose one permitted execution; universal correctness
continues to allow all result encodings admitted by FP.Result. -/
def words (input : Nat → Word) : Nat → Nat → Word
  | 0 => input
  | k+1 => fun t => if t<256 / 2^(k+1) then
      sum (words input k t) (words input k (t+256 / 2^(k+1))) else words input k t

/-- Exact words carried by the constructed trace, not an assumption in the
universal numerical theorem. Barrier records impose no numerical condition. -/
def Expected (input : Nat → Word) : Event 256 → Prop
  | .barrier _ => True
  | .data t a =>
    (∀ phase : Fin 9, a.data.pc=site phase → a.data.value=words input phase.val t.val) ∧
    (∀ (k : Fin 8) (right : Bool), a.data.pc=readPC k right →
      a.data.value=words input k.val (t.val+(if right then active (current k) else 0)))

theorem initial_expected (s : PTX.State) (thread : Fin 256)
    (pc : s.pc=0) (value : s.regs 8=input thread.val)
    (a : Access) (member : a∈initialEvents s) : Expected input (.data thread a) := by
  simp only [initialEvents,List.mem_singleton] at member
  subst a
  constructor
  · intro phase atSite
    have zero : phase.val=0 := by simp only [pc,site] at atSite; omega
    simpa only [zero,words] using value
  · intro k right atRead
    cases right <;> simp only [pc,readPC,Bool.false_eq_true,↓reduceIte] at atRead <;> omega

theorem update_expected (input : Nat → Word) (s : PTX.State) (k : Fin 8) (thread : Fin 256)
    (pc : s.pc=5+8*k.val) (live : thread.val<active (current k))
    (a : Access) (member : a∈updateEvents s (readOffset k true)
      (words input k.val thread.val) (words input k.val (thread.val+active (current k)))) :
    Expected input (.data thread a) := by
  simp only [updateEvents,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl|rfl|rfl
  · constructor
    · intro phase atSite; simp only [pc,site] at atSite; omega
    · intro q right atRead
      cases right
      · have eq : q.val=k.val := by simp only [pc,readPC,Bool.false_eq_true,↓reduceIte] at atRead; omega
        simp only [eq,Bool.false_eq_true,↓reduceIte,Nat.add_zero]
      · simp only [pc,readPC,↓reduceIte] at atRead; omega
  · constructor
    · intro phase atSite; simp only [pc,site] at atSite; omega
    · intro q right atRead
      cases right
      · simp only [pc,readPC,Bool.false_eq_true,↓reduceIte] at atRead; omega
      · have eq : q=k := by apply Fin.ext; simp only [pc,readPC,↓reduceIte] at atRead; omega
        subst q; rfl
  · constructor
    · intro phase atSite
      have eq : phase.val=k.val+1 := by simp only [pc,site] at atSite; omega
      rw [eq,words]
      simp only [show thread.val<256 / 2^(k.val+1) from live,↓reduceIte]
      rfl
    · intro q right atRead
      cases right <;> simp only [pc,readPC,Bool.false_eq_true,↓reduceIte] at atRead <;> omega

end PtxTorchLean.Poisson.PTX.Concurrent.Reduction.Control.Witness256

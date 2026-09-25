import PtxBinary32.Dot
import PtxBinary32.SquareError

/-! Numerical conditions and accumulated errors are functions of initial input
values and the prescribed rounding order. No intermediate accuracy is assumed. -/
namespace Ptx.Binary32.DotError
open TorchLean.Floats (eps32)

/-- Actual encoded values, ideal values and their incoming error bounds. -/
structure Input where
  left : Word
  right : Word
  lh : ℝ
  rh : ℝ
  l : ℝ
  r : ℝ
  el : ℝ
  er : ℝ
  leftReal : finiteReal left = some lh
  rightReal : finiteReal right = some rh
  leftError : |lh-l| ≤ el
  rightError : |rh-r| ≤ er
  productRange : |lh*rh| ≤ Bounds.maxFinite

def words (xs : List Input) : List (Word × Word) := xs.map fun x => (x.left,x.right)
noncomputable def step (x : Input) (acc : ℝ) : ℝ := SquareError.roundedAffine x.lh x.rh acc
noncomputable def rounded : List Input → ℝ → ℝ
  | [], acc => acc
  | x::xs, acc => rounded xs (step x acc)
noncomputable def ideal (xs : List Input) (acc : ℝ) : ℝ := acc + (xs.map fun x => x.l*x.r).sum

/-- Bounds on each addition are calculated from the initial inputs and the
explicit rounded prefix; no actual intermediate word occurs in this guard. -/
def Safe : List Input → ℝ → Prop
  | [], _ => True
  | x::xs, acc => |x.lh*x.rh| + eps32 (x.lh*x.rh) + |acc| ≤ Bounds.maxFinite ∧ Safe xs (step x acc)

/-- Two local rounding allowances plus input encoding error, summed over the
prescribed rounded prefixes. An incoming accumulator error is added separately. -/
noncomputable def budget : List Input → ℝ → ℝ
  | [], _ => 0
  | x::xs, acc => Error.affineBudget x.lh x.rh acc x.l x.r x.el x.er 0 + budget xs (step x acc)

theorem ideal_cons (x : Input) (xs : List Input) (acc : ℝ) :
    ideal (x::xs) acc = ideal xs (x.l*x.r+acc) := by
  simp [ideal]; ring

/-- Finiteness and the final error are derived for every admitted accumulation. -/
theorem fold_accuracy (xs : List Input) (acc out : Word) (ah a error : ℝ)
    (accReal : finiteReal acc = some ah) (accError : |ah-a| ≤ error)
    (safe : Safe xs ah) (allowed : Scalar.Dot.Fold (words xs) acc out) :
    finiteReal out = some (rounded xs ah) ∧ |rounded xs ah-ideal xs a| ≤ error+budget xs ah := by
  induction xs generalizing acc out ah a error with
  | nil =>
    cases allowed
    exact ⟨accReal,by simpa [rounded,ideal,budget] using accError⟩
  | cons x xs ih =>
    cases allowed with
    | @cons _ _ product next _ _ pair rest =>
      have value := SquareError.affine_value x.left x.right acc product next x.lh x.rh ah
        x.leftReal x.rightReal accReal x.productRange safe.1 pair
      obtain ⟨_,_,z,hz,herr⟩ := Error.affine_results x.left x.right acc product next
        x.lh x.rh ah x.l x.r a x.el x.er error
        x.leftReal x.rightReal accReal x.productRange safe.1 x.leftError x.rightError accError pair
      have zeq : z = step x ah := Option.some.inj (hz.symm.trans value)
      subst z
      obtain ⟨outReal,outError⟩ := ih next out (step x ah) (x.l*x.r+a)
        (Error.affineBudget x.lh x.rh ah x.l x.r x.el x.er error) value herr safe.2 rest
      refine ⟨outReal,?_⟩
      rw [ideal_cons]
      simpa [rounded,budget,Error.affineBudget,add_assoc,add_comm,add_left_comm] using outError

/-- Accuracy of the actual final stored word; all numeric hypotheses concern
initial inputs and explicit rounded expressions in them. -/
theorem stored_accuracy (xs : List Input)
    (bounds : Scalar.Dot.Bounds s.memory left right (words xs))
    (stored : Scalar.Dot.Stored s.memory left right (words xs))
    (outBound : output < s.memory.length) (outPointer : 4*output < 2^64)
    (safe : Safe xs 0)
    (run : Scalar.Mixed.Run target Scalar.Dot.program
      (Scalar.Dot.initial s left right output xs.length) final status events) :
    status = .halted ∧ ∃ out,
      final.memory[output]? = some out ∧ finiteReal out = some (rounded xs 0) ∧
      |rounded xs 0-(xs.map fun x => x.l*x.r).sum| ≤ budget xs 0 := by
  have run' : Scalar.Mixed.Run target Scalar.Dot.program
      (Scalar.Dot.initial s left right output (words xs).length) final status events := by
    simpa [words] using run
  obtain ⟨hs,_,out,fold,memory⟩ := Scalar.Dot.correct bounds stored outBound outPointer run'
  obtain ⟨value,error⟩ := fold_accuracy xs 0 out 0 0 0 SquareError.zero_real (by simp) safe fold
  refine ⟨hs,out,?_,value,by simpa [ideal] using error⟩
  simp [memory,outBound]

end Ptx.Binary32.DotError

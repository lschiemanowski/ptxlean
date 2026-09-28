import PoissonQuadCorrespondence
import FloatLib.Floats.Formats.BinaryInterchange.Dyadic.Decode
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! An exact a posteriori checker for GPU Poisson results. The solver is
untrusted. Acceptance is a rational inequality for the SAME represented
coefficient arrays, not a floating-point residual with an empirical allowance. -/
namespace PtxTorchLean.Poisson.Certificate
open TorchLean Correspondence

/-- Mesh and coefficient values define the discrete problem. These rational
values are exact interpretations of the binary64 setup words, not recomputed
ideal quadrature. Their approximation to the continuous PDE is separate. -/
structure Problem (e n v : Nat) where
  mesh : Connectivity e n v
  b : Mat ℚ n n
  d : Mat ℚ n n
  w : Mat ℚ n n
  rhs : Fin v → ℚ
  boundary : Fin v → Bool
  rtol : ℚ
  atol : ℚ

def exactApply (p : Problem e n v) (x : Fin v → ℚ) : Fin v → ℚ :=
  tensorOperator p.mesh p.b p.d p.w x

def residual (p : Problem e n v) (x : Fin v → ℚ) : Fin v → ℚ :=
  let applied := exactApply p x
  fun i => if p.boundary i then 0 else p.rhs i - applied i

def squareSum (x : Fin v → ℚ) : ℚ :=
  (List.finRange v).foldl (fun acc i => acc + x i * x i) 0

def rhsSquare (p : Problem e n v) : ℚ :=
  squareSum fun i => if p.boundary i then 0 else p.rhs i

def thresholdSquare (p : Problem e n v) : ℚ :=
  max (p.atol*p.atol) (p.rtol*p.rtol*rhsSquare p)

def Accepts (p : Problem e n v) (x : Fin v → ℚ) : Prop :=
  0 ≤ p.atol ∧ 0 ≤ p.rtol ∧
  (∀ i, p.boundary i = true → x i = 0) ∧
  squareSum (residual p x) ≤ thresholdSquare p

instance (p : Problem e n v) (x : Fin v → ℚ) : Decidable (Accepts p x) := by
  unfold Accepts; infer_instance

/-- Eager vector storage for efficient exact assembly. -/
def scatterVectorStep (s : Vector ℚ v) (entry : Fin v × ℚ) : Vector ℚ v :=
  s.set entry.1 (s[entry.1] + entry.2)

theorem scatterVectorStep_get (s : Vector ℚ v) (entry : Fin v × ℚ) :
    (fun i => (scatterVectorStep s entry)[i]) = scatterStep (fun i => s[i]) entry := by
  funext i
  simp only [scatterVectorStep, scatterStep, Function.update_apply]
  by_cases h : i = entry.1
  · subst i; simp
  · have hn : i.val ≠ entry.1.val := fun hval => h (Fin.ext hval)
    simp [h, Ne.symm hn]

theorem scatterVector_fold (xs : List (Fin v × ℚ)) (s : Vector ℚ v) :
    (fun i => (xs.foldl scatterVectorStep s)[i]) =
      xs.foldl scatterStep (fun i => s[i]) := by
  induction xs generalizing s with
  | nil => rfl
  | cons entry xs ih =>
    simp only [List.foldl_cons, ih, scatterVectorStep_get]

def computedApply (p : Problem e n v) (x : Fin v → ℚ) : Vector ℚ v :=
  (tensorContributions p.mesh p.b p.d p.w x).foldl scatterVectorStep (Vector.replicate v 0)

theorem computedApply_get (p : Problem e n v) (x : Fin v → ℚ) (i : Fin v) :
    (computedApply p x)[i] = exactApply p x i := by
  have h := congrFun (scatterVector_fold (tensorContributions p.mesh p.b p.d p.w x)
    (Vector.replicate v 0)) i
  simpa [computedApply, exactApply, tensorOperator] using h

def computedResidual (p : Problem e n v) (x : Fin v → ℚ) : Vector ℚ v :=
  let applied := computedApply p x
  Vector.ofFn fun i => if p.boundary i then 0 else p.rhs i - applied[i]

theorem computedResidual_get (p : Problem e n v) (x : Fin v → ℚ) (i : Fin v) :
    (computedResidual p x)[i] = residual p x i := by
  change (Vector.ofFn (fun j : Fin v => if p.boundary j then 0 else
    p.rhs j - (computedApply p x)[j]))[i.val] = residual p x i
  rw [Vector.getElem_ofFn]
  unfold residual
  split
  · rfl
  · exact congrArg (fun z => p.rhs i-z) (computedApply_get p x i)

def computedSquare (p : Problem e n v) (x : Fin v → ℚ) : ℚ :=
  let r := computedResidual p x
  squareSum fun i => r[i]

theorem computedSquare_eq (p : Problem e n v) (x : Fin v → ℚ) :
    computedSquare p x = squareSum (residual p x) := by
  simp only [computedSquare, computedResidual_get]

def check (p : Problem e n v) (x : Fin v → ℚ) : Bool :=
  decide (0 ≤ p.atol ∧ 0 ≤ p.rtol ∧
    (∀ i, p.boundary i = true → x i = 0) ∧ computedSquare p x ≤ thresholdSquare p)

noncomputable def realNorm (x : Fin v → ℚ) : ℝ :=
  Real.sqrt ((squareSum x : ℚ) : ℝ)

/-- Checked acceptance includes the exact boundary and residual conditions. -/
theorem check_sound (p : Problem e n v) (x : Fin v → ℚ) (h : check p x = true) :
    Accepts p x := by
  simpa only [check, computedSquare_eq, decide_eq_true_eq, Accepts] using h

/-- Norm squared is the ordinary sum of squared coordinates. -/
theorem squareSum_eq_sum (x : Fin v → ℚ) : squareSum x = ∑ i, x i * x i := by
  have fold (xs : List (Fin v)) (a : ℚ) :
      xs.foldl (fun acc i => acc+x i*x i) a = a + (xs.map fun i => x i*x i).sum := by
    induction xs generalizing a with
    | nil => simp
    | cons i xs ih => simp [ih, add_assoc]
  simp [squareSum, fold, List.finRange, List.map_ofFn, List.sum_ofFn]

theorem squareSum_nonneg (x : Fin v → ℚ) : 0 ≤ squareSum x := by
  rw [squareSum_eq_sum]
  exact Finset.sum_nonneg fun i _ => mul_self_nonneg (x i)

/-- Casting the exact rational check gives the Euclidean norm over real numbers. -/
theorem realNorm_eq (x : Fin v → ℚ) :
    realNorm x = Real.sqrt (∑ i, (x i : ℝ)^2) := by
  simp [realNorm, squareSum_eq_sum, pow_two]

/-- No hypothesis says that the GPU computes the operator correctly. Any vector
accepted by the exact checker meets the requested mathematical residual bound. -/
theorem certified_residual (p : Problem e n v) (x : Fin v → ℚ)
    (accepted : check p x = true) :
    (∀ i, p.boundary i = true → x i = 0) ∧
      realNorm (residual p x) ≤
        max (p.atol : ℝ) ((p.rtol : ℝ) * realNorm (fun i => if p.boundary i then 0 else p.rhs i)) := by
  obtain ⟨ha,hr,hboundary,hbound⟩ := check_sound p x accepted
  refine ⟨hboundary, ?_⟩
  have ha' : (0 : ℝ) ≤ p.atol := by exact_mod_cast ha
  have hr' : (0 : ℝ) ≤ p.rtol := by exact_mod_cast hr
  have bound : ((squareSum (residual p x) : ℚ) : ℝ) ≤ ((thresholdSquare p : ℚ) : ℝ) := by exact_mod_cast hbound
  apply (Real.sqrt_le_sqrt bound).trans_eq
  simp only [thresholdSquare, Rat.cast_max, Rat.cast_mul]
  rw [(show Monotone Real.sqrt from fun _ _ h => Real.sqrt_le_sqrt h).map_max, Real.sqrt_mul (mul_nonneg hr' hr')]
  simp only [Real.sqrt_mul_self ha', Real.sqrt_mul_self hr', realNorm, rhsSquare]

end PtxTorchLean.Poisson.Certificate

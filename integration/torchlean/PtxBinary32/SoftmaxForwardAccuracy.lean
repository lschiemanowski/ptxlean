import PtxBinary32.SumCorrect
import PtxBinary32.SoftmaxNormalize
import PtxBinary32.ShiftedExpRange

/-! Numerical composition of the concrete arithmetic stages of a stable
softmax row. The memory controller must establish these relations from its
actual loads, runs and stores; this module assumes no intermediate error or
finiteness certificate from that controller. -/
namespace Ptx.Binary32.SoftmaxForward
open TorchLean.Floats (round32 eps32)
open Ptx.Numerics.Softmax
open scoped BigOperators
noncomputable section

/-- The four arithmetic stages keep their actual intermediate encoded operands. -/
def ExpStages (input maximum output : Word) : Prop :=
  ∃ negative shifted product,
    Results .mul maximum 0xbf800000 negative ∧
    Results .add input negative shifted ∧
    Results .mul shifted ExpArgument.constantWord product ∧
    Exponential.Results product output

/-- Initial-score error allowance; no actual intermediate value occurs here. -/
def delta (x m : ℝ) : ℝ := 5/(2:ℝ)^24 + Real.log 2 *
  ExpArgument.budget (round32 (x-m)) (eps32 (x-m))

def exact (values : Fin n → ℝ) (m : ℝ) (i : Fin n) : ℝ := Real.exp (values i-m)

def totalBudget (depth : Nat) (values : Fin (2^depth) → ℝ) (m : ℝ) : ℝ :=
  denominatorBudget (fun i => delta (values i) m) (SumTree.budget depth)

/-- Equal-score rows satisfy the input accuracy guard. This verifies a
nonempty input family for every supported row length, without assuming
intermediate values or successful executions. -/
theorem equal_scores_guard (depth : Nat) (bound : depth≤10) (m : ℝ) :
    totalBudget depth (fun _ => m) m≤1/2 := by
  have lp : 0<Real.log 2 := Real.log_pos (by norm_num)
  have lu : Real.log 2≤1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
    norm_num at h
    exact h
  have ep : eps32 0=(2:ℝ)^(-150:ℤ) := by
    change TorchLean.Floats.ulp32 0 / 2 = _
    rw [TorchLean.Floats.ulp32_zero]
    norm_num [FloatLib.Floats.Formats.Flocq.bpow,FloatLib.Numerics.binaryRadix,FloatLib.Numerics.Radix.toReal]
  have de : delta m m≤1/1048576 := by
    have zero : round32 0=0 := FloatLib.Floats.Formats.BinaryInterchange.Model.roundAt_zero FloatLib.Floats.Formats.BinaryInterchange.FloatFormat.binary32
    unfold delta ExpArgument.budget
    simp only [sub_self,zero,zero_mul,abs_zero,add_zero,ep]
    rw [mul_add, mul_div_cancel₀ _ (ne_of_gt lp)]
    have h := mul_le_mul_of_nonneg_right lu (by positivity : (0:ℝ)≤(2:ℝ)^(-150:ℤ))
    norm_num at h ⊢
    linarith
  have sumBound : (∑_i : Fin (2^depth),delta m m)≤1024/1048576 := by
    calc
      _≤∑_i : Fin (2^depth),(1:ℝ)/1048576 := Finset.sum_le_sum (fun _ _ => de)
      _=((2:ℝ)^depth)/1048576 := by simp [div_eq_mul_inv]
      _≤1024/1048576 := by
        apply div_le_div_of_nonneg_right _ (by norm_num)
        have h := pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2) bound
        norm_num at h
        exact h
  have budget := SumTree.budget_bound depth bound
  unfold totalBudget denominatorBudget
  linarith

/-- Derive finite exponential values and their errors from the actual stage
relations. The approximation may return a negative value near zero. -/
theorem exponentials (input outputs : Fin n → Word) (maximum : Word)
    (values : Fin n → ℝ) (m : ℝ)
    (inputs : ∀i, finiteReal (input i)=some (values i))
    (maximumValue : finiteReal maximum=some m)
    (upper : ∀i, values i≤m) (attained : ∃i, values i=m)
    (small : ∀i, |values i|≤(2:ℝ)^(124:ℤ))
    (stages : ∀i, ExpStages (input i) maximum (outputs i)) :
    ∃ u : Fin n → ℝ, (∀i, finiteReal (outputs i)=some (u i)) ∧
      (∀i, |u i|≤2) ∧ (∀i, |u i-exact values m i|≤delta (values i) m) := by
  have maxSmall : |m|≤(2:ℝ)^(124:ℤ) := by
    obtain ⟨i,hi⟩ := attained
    simpa only [hi] using small i
  have each (i : Fin n) : ∃ u : ℝ, finiteReal (outputs i)=some u ∧
      |u|≤2 ∧ |u-exact values m i|≤delta (values i) m := by
    obtain ⟨negative,shifted,product,r₀,r₁,r₂,r₃⟩ := stages i
    have bounds : ShiftedExp.InputBounds (values i) m := ⟨upper i,small i,maxSmall⟩
    obtain ⟨u,hu,error⟩ := ShiftedExp.error (input i) maximum negative shifted product (outputs i)
      (values i) m (inputs i) maximumValue bounds r₀ r₁ r₂ r₃
    obtain ⟨v,hv,mag⟩ := ShiftedExp.output_range (input i) maximum negative shifted product (outputs i)
      (values i) m (inputs i) maximumValue bounds r₀ r₁ r₂ r₃
    have eq : v=u := Option.some.inj (hv.symm.trans hu)
    subst v
    exact ⟨u,hu,mag,error⟩
  choose u hu hm he using each
  exact ⟨u,hu,hm,he⟩

/-- An attained maximum makes one ideal exponential exactly one, while all
others lie in (0,1]. Thus the ideal denominator is at least one. -/
theorem exact_bounds (values : Fin n → ℝ) (m : ℝ)
    (upper : ∀i, values i≤m) (attained : ∃i, values i=m) :
    (∀i, 0≤exact values m i) ∧ (∀i, exact values m i≤1) ∧
    1≤∑i,exact values m i := by
  have nonneg (i : Fin n) : 0≤exact values m i := (Real.exp_pos _).le
  have bounded (i : Fin n) : exact values m i≤1 :=
    Real.exp_le_one_iff.mpr (sub_nonpos.mpr (upper i))
  have witness : ∃i, exact values m i=1 := by
    obtain ⟨i,hi⟩ := attained
    exact ⟨i,by simp [exact,hi]⟩
  exact ⟨nonneg,bounded,(exact_denominator_bounds _ nonneg bounded witness).1⟩

/-- Full numerical aggregation: every intermediate interpretation and accuracy
bound follows from original-score conditions and actual arithmetic relations.
The total error guard is an explicit input condition, not a successful-output
assumption. The theorem does not assert a memory or launch correspondence. -/
theorem correct (depth : Nat) (bound : depth≤10)
    (input exponentials outputs : Fin (2^depth) → Word) (maximum denominator : Word)
    (values : Fin (2^depth) → ℝ) (m : ℝ)
    (inputs : ∀i, finiteReal (input i)=some (values i))
    (maximumValue : finiteReal maximum=some m)
    (upper : ∀i, values i≤m) (attained : ∃i, values i=m)
    (small : ∀i, |values i|≤(2:ℝ)^(124:ℤ))
    (expStages : ∀i, ExpStages (input i) maximum (exponentials i))
    (summation : Scalar.Parallel.Sum.Output depth exponentials denominator)
    (normalization : ∀i, Normalize.Stages (exponentials i) denominator (outputs i))
    (guard : totalBudget depth values m≤1/2) :
    ∃ u : Fin (2^depth) → ℝ,
      (∀i, finiteReal (exponentials i)=some (u i)) ∧
      finiteReal denominator=some (Scalar.Parallel.Sum.rounded depth u) ∧
      1/2≤Scalar.Parallel.Sum.rounded depth u ∧
      (∀i, finiteReal (outputs i)=some (round32 (u i*round32 (1/Scalar.Parallel.Sum.rounded depth u)))) ∧
      (∀i, |round32 (u i*round32 (1/Scalar.Parallel.Sum.rounded depth u))-
          exact values m i/(∑j,exact values m j)|≤
        coordinateBudget (delta (values i) m) (totalBudget depth values m)
          (eps32 (1/Scalar.Parallel.Sum.rounded depth u))
          (eps32 (u i*round32 (1/Scalar.Parallel.Sum.rounded depth u)))) ∧
      |(∑i,round32 (u i*round32 (1/Scalar.Parallel.Sum.rounded depth u)))-1|≤
        ∑i,coordinateBudget (delta (values i) m) (totalBudget depth values m)
          (eps32 (1/Scalar.Parallel.Sum.rounded depth u))
          (eps32 (u i*round32 (1/Scalar.Parallel.Sum.rounded depth u))) := by
  obtain ⟨u,finite,mag,errors⟩ := SoftmaxForward.exponentials input exponentials maximum values m
    inputs maximumValue upper attained small expStages
  obtain ⟨sumValue,_,sumError⟩ := Scalar.Parallel.Sum.output_accuracy depth bound exponentials u denominator
    finite mag summation
  obtain ⟨nonneg,bounded,lower⟩ := exact_bounds values m upper attained
  have den := SoftmaxNormalize.denominator_lower (exact values m) u (fun i => delta (values i) m)
    (Scalar.Parallel.Sum.rounded depth u) (SumTree.budget depth) errors sumError lower guard
  obtain ⟨outputValues,stages⟩ := SoftmaxNormalize.encoded_stages (exact values m) u
    (fun i => delta (values i) m) (Scalar.Parallel.Sum.rounded depth u) (SumTree.budget depth)
    exponentials outputs denominator finite sumValue nonneg bounded lower errors sumError guard normalization
  have less : denominatorBudget (fun i => delta (values i) m) (SumTree.budget depth)<1 := by
    change totalBudget depth values m<1
    linarith
  exact ⟨u,finite,sumValue,den,outputValues,
    fun i => coordinate_error stages nonneg bounded lower less i,
    normalization_error stages nonneg bounded lower less⟩

end
end Ptx.Binary32.SoftmaxForward

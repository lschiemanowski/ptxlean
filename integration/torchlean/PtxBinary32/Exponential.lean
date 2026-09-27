import PtxBinary32.ExpArgument

/-! Partial arithmetic provider for the selected non-FTZ approximate exponential.
Positive finite operands are unsupported, not undefined. The finite allowance
covers the two named ULP interpretations; it does not resolve source ambiguity.
There is no fetched instruction or execution semantics in this module. -/
namespace Ptx.Binary32.Exponential
noncomputable section

/-- Supported operands include every special value and finite nonpositive reals. -/
def Supported (input : Word) : Prop :=
  isNaN input = true ∨ input = 0xff800000 ∨ input = 0x7f800000 ∨
    ∃ x : ℝ, finiteReal input = some x ∧ x ≤ 0

/-- Exact special cases take precedence over a finite approximate allowance.
The output is unrestricted within the conservative envelope for negative inputs. -/
def Results (input output : Word) : Prop :=
  (isNaN input = true ∧ isNaN output = true) ∨
  (input = 0xff800000 ∧ output = 0) ∨
  (input = 0x7f800000 ∧ output = 0x7f800000) ∨
  ∃ x : ℝ, finiteReal input = some x ∧ x ≤ 0 ∧
    if x = 0 then output = 0x3f800000 else ConservativeULP.Results ((2:ℝ)^x) output

private theorem finite_ne_infinities (input : Word) (x : ℝ)
    (value : finiteReal input = some x) : input ≠ 0xff800000 ∧ input ≠ 0x7f800000 := by
  constructor <;> intro h <;> subst input <;>
    rw [finiteReal_none _ (by decide)] at value <;> contradiction

/-- On a finite operand this characterizes every result, including exact zero. -/
theorem finite_iff (input output : Word) (x : ℝ) (value : finiteReal input = some x) :
    Results input output ↔ x ≤ 0 ∧
      if x = 0 then output = 0x3f800000 else ConservativeULP.Results ((2:ℝ)^x) output := by
  have hn := finite_not_nan input (Bounds.finiteReal_spec input x value).1
  have hi := finite_ne_infinities input x value
  simp only [Results, hn, Bool.false_eq_true, false_and, false_or,
    hi.1, hi.2, value, Option.some.injEq]
  simp

/-- Zero has the exact positive-one result, regardless of the input zero sign. -/
theorem zero_iff (input output : Word) (value : finiteReal input = some 0) :
    Results input output ↔ output = 0x3f800000 := by
  simp [finite_iff input output 0 value]

/-- Every envelope output remains admitted; there is no hidden nonnegativity or
normal-number restriction on returned finite values. -/
theorem negative_iff (input output : Word) (x : ℝ)
    (value : finiteReal input = some x) (negative : x < 0) :
    Results input output ↔ ConservativeULP.Results ((2:ℝ)^x) output := by
  rw [finite_iff input output x value]
  simp [negative.le, ne_of_lt negative]

/-- Positive finite arguments have no result in this partial provider. -/
theorem positive_unsupported (input : Word) (x : ℝ)
    (value : finiteReal input = some x) (positive : 0 < x) : ¬ Supported input := by
  have hn := finite_not_nan input (Bounds.finiteReal_spec input x value).1
  have hi := finite_ne_infinities input x value
  simp only [Supported, hn, hi.1, hi.2, value, Bool.false_eq_true, false_or]
  simp [not_le.mpr positive]

/-- NaN payload freedom is conservative: individual payload realizability is not asserted. -/
theorem nan_iff (input output : Word) (nan : isNaN input = true) :
    Results input output ↔ isNaN output = true := by
  have ni : input ≠ 0xff800000 := by intro h; subst input; contradiction
  have pi : input ≠ 0x7f800000 := by intro h; subst input; contradiction
  have nv : ∀ x : ℝ, finiteReal input ≠ some x := by
    intro x value
    have := finite_not_nan input (Bounds.finiteReal_spec input x value).1
    simp_all
  simp only [Results, nan, ni, pi, nv, true_and, false_and, false_or]
  simp

theorem neg_inf_iff (output : Word) : Results 0xff800000 output ↔ output = 0 := by
  have hn : isNaN (0xff800000 : Word) = false := by decide
  simp only [Results, hn, finiteReal_none _ (by decide : isFinite (0xff800000 : Word) = false)]
  norm_num

theorem pos_inf_iff (output : Word) : Results 0x7f800000 output ↔ output = 0x7f800000 := by
  have hn : isNaN (0x7f800000 : Word) = false := by decide
  simp only [Results, hn, finiteReal_none _ (by decide : isFinite (0x7f800000 : Word) = false)]
  norm_num

/-- Numerical existence holds exactly on the advertised domain. -/
theorem results_exists_iff (input : Word) : (∃ output, Results input output) ↔ Supported input := by
  constructor
  · rintro ⟨output, nan | negInf | posInf | ⟨x,value,nonpos,_⟩⟩
    · exact Or.inl nan.1
    · exact Or.inr (Or.inl negInf.1)
    · exact Or.inr (Or.inr (Or.inl posInf.1))
    · exact Or.inr (Or.inr (Or.inr ⟨x,value,nonpos⟩))
  · intro supported
    rcases supported with nan | negInf | posInf | ⟨x,value,nonpos⟩
    · exact ⟨input, (nan_iff input input nan).mpr nan⟩
    · subst input; exact ⟨0, (neg_inf_iff 0).mpr rfl⟩
    · subst input; exact ⟨0x7f800000, (pos_inf_iff _).mpr rfl⟩
    · by_cases zero : x = 0
      · subst x; exact ⟨0x3f800000, (zero_iff _ _ value).mpr rfl⟩
      · obtain ⟨output,h⟩ := ConservativeULP.exp2_results_exists x nonpos
        exact ⟨output, (negative_iff _ _ x value (lt_of_le_of_ne nonpos zero)).mpr h⟩

theorem results_supported {input output : Word} (allowed : Results input output) :
    Supported input := (results_exists_iff input).mp ⟨output,allowed⟩

/-- Convenience form used by instruction existence proofs. -/
theorem results_exists (input : Word) (supported : Supported input) :
    ∃ output, Results input output := (results_exists_iff input).mpr supported

/-- Exact one belongs to the broad finite envelope, enabling a bridge while
retaining the stronger exact-zero contract in this provider. -/
theorem one_allowed : ConservativeULP.Results 1 0x3f800000 := by
  have center := RoundedReal.word_preserves_value 0x3f800000 1 Approximate.one_real
    (RoundedReal.unit_range 1 (by norm_num) (by norm_num))
  refine ⟨1,1,center,Approximate.one_real,?_⟩
  simp only [sub_self, abs_zero]
  exact mul_nonneg (by norm_num) (le_max_of_le_left (Approximate.ulp_nonnegative 1))

/-- Every permitted finite result feeds the previously proved argument bridge. -/
theorem finiteExp2 (input output : Word) (x : ℝ) (value : finiteReal input = some x)
    (allowed : Results input output) : ExpArgument.FiniteExp2 input output := by
  obtain ⟨nonpos,h⟩ := (finite_iff input output x value).mp allowed
  refine ⟨x,value,nonpos,?_⟩
  by_cases zero : x = 0
  · subst x
    simp only [ite_true] at h
    subst output
    simpa using one_allowed
  · simpa [zero] using h

/-- All-result error, with output finiteness derived rather than hypothesized. -/
theorem finite_error (input output : Word) (x : ℝ) (value : finiteReal input = some x)
    (allowed : Results input output) :
    ∃ z : ℝ, finiteReal output = some z ∧ |z-(2:ℝ)^x| ≤ 5/(2:ℝ)^24 := by
  obtain ⟨a,ha,nonpos,h⟩ := finiteExp2 input output x value allowed
  have same : a = x := Option.some.inj (ha.symm.trans value)
  subst a
  exact ConservativeULP.exp2_error x output nonpos h

end
end Ptx.Binary32.Exponential

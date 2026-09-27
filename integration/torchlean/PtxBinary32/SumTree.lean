import PtxBinary32.Reduction
import PtxBinary32.RoundedReal
import PtxBinary32.SquareError
import PtxBinary32.ConservativeULP
import FloatLib.Floats.Formats.Flocq.Theory.Analysis.Ulp

/-! A bounded binary32 sum, using the actual multiply-by-one leaves of the
existing dense kernel. Range checks are derived from the original finite row,
including negative entries, rather than postulated for intermediate nodes. -/
namespace Ptx.Binary32.SumTree
open TorchLean.Floats (round32 eps32 ulp32 fexp32 rnd32)
open FloatLib.Floats.Formats.BinaryInterchange (Model FloatFormat)
open FloatLib.Floats.Formats.Flocq
open FloatLib.Numerics
noncomputable section

private theorem power_fixed (k : Nat) : round32 ((2:ℝ)^k) = (2:ℝ)^k := by
  have h : genericFormat binaryRadix fexp32 (bpow binaryRadix (k:ℤ)) := by
    apply generic_format_bpow
    change max ((k:ℤ)+1-24) (-149) ≤ k
    omega
  have eq : bpow binaryRadix (k:ℤ) = (2:ℝ)^k := by simp [bpow,binaryRadix,Radix.toReal]
  rw [← eq]
  exact round_preserves_generic rnd32 _ h

private theorem round_power_bound (x : ℝ) (k : Nat) (small : |x|≤(2:ℝ)^k) :
    |round32 x|≤(2:ℝ)^k := by
  have hi := Model.roundAt_mono FloatFormat.binary32 (abs_le.mp small).2
  have lo := Model.roundAt_mono FloatFormat.binary32 (abs_le.mp small).1
  change round32 x ≤ round32 ((2:ℝ)^k) at hi
  rw [power_fixed] at hi
  rw [Model.roundAt_neg] at lo
  change -round32 ((2:ℝ)^k) ≤ round32 x at lo
  rw [power_fixed] at lo
  exact abs_le.mpr ⟨lo,hi⟩

/-- A common absolute rounding allowance for every addition in a row of at
most 1024 entries, each of magnitude at most two. -/
theorem eps_bound (x : ℝ) (small : |x|≤2048) : eps32 x ≤ 1/8192 := by
  have upper := ConservativeULP.ulp_relative x
  have h : max ((2:ℝ)^(-149:ℤ)) (|x| * (2:ℝ)^(-23:ℤ)) ≤ 1/4096 := by
    apply max_le
    · norm_num
    · have := mul_le_mul_of_nonneg_right small (by positivity : (0:ℝ)≤(2:ℝ)^(-23:ℤ))
      norm_num at this ⊢
      exact this
  have result := upper.trans h
  change ulp32 x / 2 ≤ _
  linarith

/-- The prescribed balanced rounding order, indexed by a contiguous subtree. -/
def rounded (values : Nat → ℝ) : Nat → Nat → ℝ
  | 0,offset => values offset
  | k+1,offset => round32 (rounded values k offset + rounded values k (offset+2^k))

def ideal (values : Nat → ℝ) : Nat → Nat → ℝ
  | 0,offset => values offset
  | k+1,offset => ideal values k offset + ideal values k (offset+2^k)

/-- The uniform allowance counts the actual internal addition nodes. -/
def budget (depth : Nat) : ℝ := ((2:ℝ)^depth-1)/8192

theorem ideal_sum (values : Nat → ℝ) (k offset : Nat) :
    ideal values k offset = ((List.range (2^k)).map (fun j => values (offset+j))).sum := by
  induction k generalizing offset with
  | zero => simp [ideal]
  | succ k ih =>
    rw [ideal,ih,ih,pow_succ,Nat.mul_two,List.range_add,List.map_append,List.sum_append,List.map_map]
    simp [Function.comp_def,Nat.add_assoc]

private theorem finite_fixed (word : Word) (x : ℝ) (value : finiteReal word=some x) :
    round32 x=x := by
  have spec := Bounds.finiteReal_spec word x value
  have h := Model.roundAt_toReal_eq (FloatLib.Floats.ExecFloat.Binary.toModel (decode word)) spec.1
  rwa [spec.2] at h

/-- All allowed arithmetic results are finite and obey a derived error bound.
The bound permits negative leaves and requires no intermediate safety premise. -/
theorem accuracy (input : Nat → Word) (values : Nat → ℝ) (k offset : Nat) (out : Word)
    (depth : k≤10)
    (finite : ∀j, j<2^k → finiteReal (input (offset+j))=some (values (offset+j)))
    (small : ∀j, j<2^k → |values (offset+j)|≤2)
    (allowed : Reduction.Eval (Reduction.balanced k offset (fun j => (0x3f800000,input j))) out) :
    finiteReal out=some (rounded values k offset) ∧
    |rounded values k offset|≤(2:ℝ)^(k+1) ∧
    |rounded values k offset-ideal values k offset|≤budget k := by
  induction k generalizing offset out with
  | zero =>
    cases allowed with
    | leaf allowed =>
      have hv : finiteReal (input offset)=some (values offset) := by simpa using finite 0 (by decide)
      have hs : |values offset|≤2 := by simpa using small 0 (by decide)
      have range : |Bounds.exactReal .mul 1 (values offset)|≤Bounds.maxFinite := by
        simpa [Bounds.exactReal] using hs.trans (by rw [Bounds.maxFinite_eq]; norm_num)
      have result := Bounds.round_of_range .mul 0x3f800000 (input offset) out 1 (values offset)
        Bounds.positive_one_real hv range allowed
      change finiteReal out=some (round32 (1*values offset)) at result
      rw [one_mul,finite_fixed _ _ hv] at result
      exact ⟨result,by simpa [rounded] using hs,by simp [rounded,ideal,budget]⟩
  | succ k ih =>
    cases allowed with
    | @fork _ left _ right _ leftEval rightEval allowed =>
      have leftFinite : ∀j, j<2^k → finiteReal (input (offset+j))=some (values (offset+j)) := by
        intro j hj; exact finite j (by rw [pow_succ]; omega)
      have rightFinite : ∀j, j<2^k → finiteReal (input (offset+2^k+j))=some (values (offset+2^k+j)) := by
        intro j hj; simpa [Nat.add_assoc] using finite (2^k+j) (by rw [pow_succ]; omega)
      have leftSmall : ∀j, j<2^k → |values (offset+j)|≤2 := by
        intro j hj; exact small j (by rw [pow_succ]; omega)
      have rightSmall : ∀j, j<2^k → |values (offset+2^k+j)|≤2 := by
        intro j hj; simpa [Nat.add_assoc] using small (2^k+j) (by rw [pow_succ]; omega)
      obtain ⟨lv,lb,le⟩ := ih offset left (by omega) leftFinite leftSmall leftEval
      obtain ⟨rv,rb,re⟩ := ih (offset+2^k) right (by omega) rightFinite rightSmall rightEval
      let a := rounded values k offset
      let b := rounded values k (offset+2^k)
      have sb : |a+b|≤(2:ℝ)^(k+1+1) := by
        calc
          |a+b|≤|a|+|b| := abs_add_le _ _
          _≤(2:ℝ)^(k+1)+(2:ℝ)^(k+1) := add_le_add lb rb
          _=(2:ℝ)^(k+1+1) := by rw [pow_succ]; ring
      have bound : (2:ℝ)^(k+1+1)≤2048 := by
        have h := pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2) (show k+1+1≤11 by omega)
        norm_num at h ⊢
        exact h
      have range : |Bounds.exactReal .add a b|≤Bounds.maxFinite := by
        exact (sb.trans bound).trans (by rw [Bounds.maxFinite_eq]; norm_num)
      have result := Bounds.round_of_range .add left right out a b lv rv range allowed
      have roundError := (TorchLean.Floats.FP32.round_abs_error (a+b)).trans (eps_bound _ (sb.trans bound))
      refine ⟨result,round_power_bound (a+b) (k+1+1) sb,?_⟩
      change |round32 (a+b)-(ideal values k offset+ideal values k (offset+2^k))|≤budget (k+1)
      calc
        _≤|round32 (a+b)-(a+b)|+|(a+b)-(ideal values k offset+ideal values k (offset+2^k))| := abs_sub_le _ _ _
        _≤1/8192+(|a-ideal values k offset|+|b-ideal values k (offset+2^k)|) := by
          apply add_le_add roundError
          convert abs_add_le (a-ideal values k offset) (b-ideal values k (offset+2^k)) using 1
          congr 1
          ring
        _≤1/8192+(budget k+budget k) := add_le_add le_rfl (add_le_add le re)
        _=budget (k+1) := by unfold budget; rw [pow_succ]; ring

/-- The dense kernel's final addition of positive zero preserves the finite
real result. This does not assert that a negative-zero bit pattern is preserved. -/
theorem add_zero_accuracy (input output : Word) (x : ℝ)
    (value : finiteReal input=some x) (small : |x|≤2048)
    (allowed : Results .add input 0 output) : finiteReal output=some x := by
  have range : |Bounds.exactReal .add x 0|≤Bounds.maxFinite := by
    simpa [Bounds.exactReal] using small.trans (by rw [Bounds.maxFinite_eq]; norm_num)
  have result := Bounds.round_of_range .add input 0 output x 0
    value SquareError.zero_real range allowed
  change finiteReal output=some (round32 (x+0)) at result
  rwa [add_zero,finite_fixed _ _ value] at result

/-- At the largest supported row the summation allowance remains below one
eighth; exponential approximation has a separate error contribution. -/
theorem budget_bound (depth : Nat) (small : depth≤10) : budget depth < 1/8 := by
  have h := pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2) small
  norm_num at h
  unfold budget
  linarith

end
end Ptx.Binary32.SumTree

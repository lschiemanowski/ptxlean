import PtxBinary32.Reduction
import PtxBinary32.RoundedReal
import PtxBinary32.SquareError
import PtxBinary32.ConservativeULP
import FloatLib.Floats.Formats.Flocq.Theory.Analysis.Ulp

/-! Bounded binary32 backward dot products. Range checks are derived from
original finite operands, including signed sensitivities. Every leaf product and
internal addition contributes its actual rounding allowance. -/
namespace Ptx.Binary32.BackwardDot
open TorchLean.Floats (round32 eps32 ulp32 fexp32 rnd32)
open FloatLib.Floats.Formats.BinaryInterchange (Model FloatFormat)
open FloatLib.Floats.Formats.Flocq
open FloatLib.Numerics
noncomputable section

theorem power_fixed (k : Nat) : round32 ((2:ℝ)^k) = (2:ℝ)^k := by
  have h : genericFormat binaryRadix fexp32 (bpow binaryRadix (k:ℤ)) := by
    apply generic_format_bpow
    change max ((k:ℤ)+1-24) (-149) ≤ k
    omega
  have eq : bpow binaryRadix (k:ℤ) = (2:ℝ)^k := by simp [bpow,binaryRadix,Radix.toReal]
  rw [← eq]
  exact round_preserves_generic rnd32 _ h

theorem round_power_bound (x : ℝ) (k : Nat) (small : |x|≤(2:ℝ)^k) :
    |round32 x|≤(2:ℝ)^k := by
  have hi := Model.roundAt_mono FloatFormat.binary32 (abs_le.mp small).2
  have lo := Model.roundAt_mono FloatFormat.binary32 (abs_le.mp small).1
  change round32 x ≤ round32 ((2:ℝ)^k) at hi
  rw [power_fixed] at hi
  rw [Model.roundAt_neg] at lo
  change -round32 ((2:ℝ)^k) ≤ round32 x at lo
  rw [power_fixed] at lo
  exact abs_le.mpr ⟨lo,hi⟩

/-- The prescribed balanced rounding order, indexed by a contiguous subtree. -/
def rounded (g p : Nat → ℝ) : Nat → Nat → ℝ
  | 0,offset => round32 (g offset*p offset)
  | k+1,offset => round32 (rounded g p k offset + rounded g p k (offset+2^k))

def ideal (g p : Nat → ℝ) : Nat → Nat → ℝ
  | 0,offset => g offset*p offset
  | k+1,offset => ideal g p k offset + ideal g p k (offset+2^k)

/-- Actual local rounding allowances, including leaf multiplications. -/
def budget (g p : Nat → ℝ) : Nat → Nat → ℝ
  | 0,offset => eps32 (g offset*p offset)
  | k+1,offset => eps32 (rounded g p k offset+rounded g p k (offset+2^k))+
    budget g p k offset+budget g p k (offset+2^k)

theorem ideal_sum (g p : Nat → ℝ) (k offset : Nat) :
    ideal g p k offset = ((List.range (2^k)).map (fun j => g (offset+j)*p (offset+j))).sum := by
  induction k generalizing offset with
  | zero => simp [ideal]
  | succ k ih =>
    rw [ideal,ih,ih,pow_succ,Nat.mul_two,List.range_add,List.map_append,List.sum_append,List.map_map]
    simp [Function.comp_def,Nat.add_assoc]

theorem finite_fixed (word : Word) (x : ℝ) (value : finiteReal word=some x) :
    round32 x=x := by
  have spec := Bounds.finiteReal_spec word x value
  have h := Model.roundAt_toReal_eq (FloatLib.Floats.ExecFloat.Binary.toModel (decode word)) spec.1
  rwa [spec.2] at h

/-- Finiteness and error from original operand bounds, for every allowed result. -/
theorem accuracy (g p : Nat → Word) (gv pv : Nat → ℝ) (k offset : Nat) (out : Word)
    (depth : k≤10)
    (finiteG : ∀j, j<2^k → finiteReal (g (offset+j))=some (gv (offset+j)))
    (finiteP : ∀j, j<2^k → finiteReal (p (offset+j))=some (pv (offset+j)))
    (smallG : ∀j, j<2^k → |gv (offset+j)|≤(2:ℝ)^60)
    (smallP : ∀j, j<2^k → |pv (offset+j)|≤4)
    (allowed : Reduction.Eval (Reduction.balanced k offset (fun j => (g j,p j))) out) :
    finiteReal out=some (rounded gv pv k offset) ∧
    |rounded gv pv k offset|≤(2:ℝ)^(k+62) ∧
    |rounded gv pv k offset-ideal gv pv k offset|≤budget gv pv k offset := by
  induction k generalizing offset out with
  | zero =>
    cases allowed with
    | leaf allowed =>
      have hg : finiteReal (g offset)=some (gv offset) := by simpa using finiteG 0 (by decide)
      have hp : finiteReal (p offset)=some (pv offset) := by simpa using finiteP 0 (by decide)
      have sg : |gv offset|≤(2:ℝ)^60 := by simpa using smallG 0 (by decide)
      have sp : |pv offset|≤4 := by simpa using smallP 0 (by decide)
      have bound : |gv offset*pv offset|≤(2:ℝ)^62 := by
        rw [abs_mul]
        calc
          _ ≤ (2:ℝ)^60*4 := mul_le_mul sg sp (abs_nonneg _) (by positivity)
          _ = _ := by norm_num
      have range : |Bounds.exactReal .mul (gv offset) (pv offset)|≤Bounds.maxFinite :=
        bound.trans (by rw [Bounds.maxFinite_eq]; norm_num)
      exact ⟨Bounds.round_of_range .mul _ _ _ _ _ hg hp range allowed,
        round_power_bound _ 62 bound,TorchLean.Floats.FP32.round_abs_error _⟩
  | succ k ih =>
    cases allowed with
    | @fork _ left _ right _ leftEval rightEval allowed =>
      have leftFiniteG : ∀j, j<2^k → finiteReal (g (offset+j))=some (gv (offset+j)) := by
        intro j hj; exact finiteG j (by rw [pow_succ]; omega)
      have rightFiniteG : ∀j, j<2^k → finiteReal (g (offset+2^k+j))=some (gv (offset+2^k+j)) := by
        intro j hj; simpa [Nat.add_assoc] using finiteG (2^k+j) (by rw [pow_succ]; omega)
      have leftFiniteP : ∀j, j<2^k → finiteReal (p (offset+j))=some (pv (offset+j)) := by
        intro j hj; exact finiteP j (by rw [pow_succ]; omega)
      have rightFiniteP : ∀j, j<2^k → finiteReal (p (offset+2^k+j))=some (pv (offset+2^k+j)) := by
        intro j hj; simpa [Nat.add_assoc] using finiteP (2^k+j) (by rw [pow_succ]; omega)
      have leftSmallG : ∀j, j<2^k → |gv (offset+j)|≤(2:ℝ)^60 := by
        intro j hj; exact smallG j (by rw [pow_succ]; omega)
      have rightSmallG : ∀j, j<2^k → |gv (offset+2^k+j)|≤(2:ℝ)^60 := by
        intro j hj; simpa [Nat.add_assoc] using smallG (2^k+j) (by rw [pow_succ]; omega)
      have leftSmallP : ∀j, j<2^k → |pv (offset+j)|≤4 := by
        intro j hj; exact smallP j (by rw [pow_succ]; omega)
      have rightSmallP : ∀j, j<2^k → |pv (offset+2^k+j)|≤4 := by
        intro j hj; simpa [Nat.add_assoc] using smallP (2^k+j) (by rw [pow_succ]; omega)
      obtain ⟨lv,lb,le⟩ := ih offset left (by omega) leftFiniteG leftFiniteP leftSmallG leftSmallP leftEval
      obtain ⟨rv,rb,re⟩ := ih (offset+2^k) right (by omega) rightFiniteG rightFiniteP rightSmallG rightSmallP rightEval
      let a := rounded gv pv k offset
      let b := rounded gv pv k (offset+2^k)
      have sb : |a+b|≤(2:ℝ)^(k+1+62) := by
        calc
          |a+b|≤|a|+|b| := abs_add_le _ _
          _≤(2:ℝ)^(k+62)+(2:ℝ)^(k+62) := add_le_add lb rb
          _=(2:ℝ)^(k+1+62) := by rw [show k+1+62=k+62+1 by omega,pow_succ]; ring
      have bound : (2:ℝ)^(k+1+62)≤(2:ℝ)^72 :=
        pow_le_pow_right₀ (by norm_num) (by omega)
      have range : |Bounds.exactReal .add a b|≤Bounds.maxFinite :=
        (sb.trans bound).trans (by rw [Bounds.maxFinite_eq]; norm_num)
      refine ⟨Bounds.round_of_range .add left right out a b lv rv range allowed,
        round_power_bound _ _ sb,?_⟩
      change |round32 (a+b)-(ideal gv pv k offset+ideal gv pv k (offset+2^k))|≤_
      calc
        _≤|round32 (a+b)-(a+b)|+|(a+b)-(ideal gv pv k offset+ideal gv pv k (offset+2^k))| := abs_sub_le _ _ _
        _≤eps32 (a+b)+(|a-ideal gv pv k offset|+|b-ideal gv pv k (offset+2^k)|) := by
          apply add_le_add (TorchLean.Floats.FP32.round_abs_error _)
          convert abs_add_le (a-ideal gv pv k offset) (b-ideal gv pv k (offset+2^k)) using 1
          congr 1
          ring
        _≤eps32 (a+b)+(budget gv pv k offset+budget gv pv k (offset+2^k)) :=
          add_le_add le_rfl (add_le_add le re)
        _=budget gv pv (k+1) offset := by simp only [budget]; ring

/-- The dense kernel's final addition of positive zero preserves the finite
real result. This does not assert that a negative-zero bit pattern is preserved. -/
theorem add_zero_accuracy (input output : Word) (x : ℝ)
    (value : finiteReal input=some x) (small : |x|≤(2:ℝ)^72)
    (allowed : Results .add input 0 output) : finiteReal output=some x := by
  have range : |Bounds.exactReal .add x 0|≤Bounds.maxFinite := by
    simpa [Bounds.exactReal] using small.trans (by rw [Bounds.maxFinite_eq]; norm_num)
  have result := Bounds.round_of_range .add input 0 output x 0
    value SquareError.zero_real range allowed
  change finiteReal output=some (round32 (x+0)) at result
  rwa [add_zero,finite_fixed _ _ value] at result

end
end Ptx.Binary32.BackwardDot

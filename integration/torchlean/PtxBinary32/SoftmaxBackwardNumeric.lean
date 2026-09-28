import PtxBinary32.BackwardDot
import PtxBinary32.ShiftedExp

/-! Arithmetic for a separately supplied softmax backward coordinate. Negate the
computed dot, add it to the incoming sensitivity, then multiply by the saved
forward weight. Finiteness follows from original operand bounds. -/
namespace Ptx.Binary32.SoftmaxBackwardNumeric
open TorchLean.Floats (round32 eps32)
noncomputable section

/-- Actual instruction order, preserving every admitted bit-level result. -/
def Result (p g dot out : Word) : Prop :=
  ∃ negative difference, Results .mul dot 0xbf800000 negative ∧
    Results .add g negative difference ∧ Results .mul p difference out

def difference (g dot : ℝ) : ℝ := round32 (g-dot)
def gradient (p g dot : ℝ) : ℝ := round32 (p*difference g dot)
def subError (g dot : ℝ) : ℝ := eps32 (g-dot)
def mulError (p g dot : ℝ) : ℝ := eps32 (p*difference g dot)

/-- Local arithmetic is nonempty even outside the finite numerical domain. -/
theorem result_exists (p g dot : Word) : ∃out, Result p g dot out := by
  obtain ⟨negative,hn⟩ := results_exists .mul dot 0xbf800000
  obtain ⟨difference,hd⟩ := results_exists .add g negative
  obtain ⟨out,ho⟩ := results_exists .mul p difference
  exact ⟨out,negative,difference,hn,hd,ho⟩

/-- No intermediate range premise is required. The multiplication by minus one
is numerically exact, including either representation of zero. -/
theorem stages (p g dot negative diff out : Word) (pv gv q : ℝ)
    (pFinite : finiteReal p=some pv) (gFinite : finiteReal g=some gv)
    (dotFinite : finiteReal dot=some q)
    (pSmall : |pv|≤4) (gSmall : |gv|≤(2:ℝ)^60) (qSmall : |q|≤(2:ℝ)^72)
    (negate : Results .mul dot 0xbf800000 negative)
    (subtract : Results .add g negative diff) (multiply : Results .mul p diff out) :
    finiteReal negative=some (-q) ∧ finiteReal diff=some (difference gv q) ∧
    finiteReal out=some (gradient pv gv q) ∧
    |difference gv q|≤(2:ℝ)^73 ∧ |gradient pv gv q|≤(2:ℝ)^75 ∧
    |difference gv q-(gv-q)|≤subError gv q ∧
    |gradient pv gv q-pv*difference gv q|≤mulError pv gv q := by
  have nq := ShiftedExp.negative_real dot negative q dotFinite
    (qSmall.trans (by norm_num)) negate
  have diffBound : |gv-q|≤(2:ℝ)^73 := by
    calc
      _ ≤ |gv|+|q| := abs_sub _ _
      _ ≤ (2:ℝ)^60+(2:ℝ)^72 := add_le_add gSmall qSmall
      _ ≤ _ := by norm_num
  have diffRange : |Bounds.exactReal .add gv (-q)|≤Bounds.maxFinite := by
    simpa [Bounds.exactReal,←sub_eq_add_neg] using
      diffBound.trans (by rw [Bounds.maxFinite_eq]; norm_num)
  have hd := Bounds.round_of_range .add g negative diff gv (-q) gFinite nq diffRange subtract
  change finiteReal diff=some (round32 (gv + -q)) at hd
  rw [←sub_eq_add_neg] at hd
  have ds : |difference gv q|≤(2:ℝ)^73 := BackwardDot.round_power_bound _ _ diffBound
  have productBound : |pv*difference gv q|≤(2:ℝ)^75 := by
    rw [abs_mul]
    calc
      _ ≤ 4*(2:ℝ)^73 := mul_le_mul pSmall ds (abs_nonneg _) (by norm_num)
      _ = _ := by norm_num
  have productRange : |Bounds.exactReal .mul pv (difference gv q)|≤Bounds.maxFinite :=
    productBound.trans (by rw [Bounds.maxFinite_eq]; norm_num)
  exact ⟨nq,hd,Bounds.round_of_range .mul p diff out pv (difference gv q)
    pFinite hd productRange multiply,ds,BackwardDot.round_power_bound _ _ productBound,
    TorchLean.Floats.FP32.round_abs_error _,TorchLean.Floats.FP32.round_abs_error _⟩

/-- Universal numerical interpretation of the three-instruction relation. -/
theorem accuracy (p g dot out : Word) (pv gv q : ℝ)
    (pFinite : finiteReal p=some pv) (gFinite : finiteReal g=some gv)
    (dotFinite : finiteReal dot=some q)
    (pSmall : |pv|≤4) (gSmall : |gv|≤(2:ℝ)^60) (qSmall : |q|≤(2:ℝ)^72)
    (allowed : Result p g dot out) :
    finiteReal out=some (gradient pv gv q) ∧
    |difference gv q-(gv-q)|≤subError gv q ∧
    |gradient pv gv q-pv*difference gv q|≤mulError pv gv q := by
  obtain ⟨negative,diff,hn,hd,ho⟩ := allowed
  have h := stages p g dot negative diff out pv gv q pFinite gFinite dotFinite
    pSmall gSmall qSmall hn hd ho
  exact ⟨h.2.2.1,h.2.2.2.2.2⟩

end
end Ptx.Binary32.SoftmaxBackwardNumeric

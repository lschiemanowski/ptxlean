import PtxBinary32Error

/-! Numerical composition for a nonempty stable-softmax row. These theorems
consume local component error contracts; they do not assert PTX execution or
representability of arbitrary real stage values. -/
namespace Ptx.Numerics.Softmax
open scoped BigOperators
noncomputable section
variable {n : ℕ} {exact approximate output delta tau : Fin n → ℝ}
  {sum reciprocal sigma rho : ℝ}

/-- Combined exponential and summation error, including dependence on row size. -/
def denominatorBudget (delta : Fin n → ℝ) (sigma : ℝ) : ℝ := sigma + ∑ i, delta i

def coordinateBudget (delta D rho tau : ℝ) : ℝ :=
  tau + (1+delta)*rho + (delta+D)/(1-D)

/-- The components expose their actual operands; no final-answer premise occurs. -/
structure Stages (exact approximate : Fin n → ℝ) (sum reciprocal : ℝ)
    (output delta : Fin n → ℝ) (sigma rho : ℝ) (tau : Fin n → ℝ) : Prop where
  exponential : ∀ i, |approximate i-exact i|≤delta i
  summation : |sum-∑ i, approximate i|≤sigma
  inverse : |reciprocal-1/sum|≤rho
  multiplication : ∀ i, |output i-approximate i*reciprocal|≤tau i

theorem sum_error (exact approximate delta : Fin n → ℝ)
    (errors : ∀ i, |approximate i-exact i|≤delta i) :
    |(∑ i, approximate i)-(∑ i, exact i)|≤∑ i, delta i := by
  rw [← Finset.sum_sub_distrib]
  exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun i _ => errors i))

theorem denominator_error (h : Stages exact approximate sum reciprocal output delta sigma rho tau) :
    |sum-∑ i, exact i|≤denominatorBudget delta sigma := by
  calc
    |sum-∑ i, exact i| = |(sum-∑ i, approximate i)+((∑ i, approximate i)-(∑ i, exact i))| := by congr 1; ring
    _ ≤ |sum-∑ i, approximate i|+|(∑ i, approximate i)-(∑ i, exact i)| := abs_add_le _ _
    _ ≤ denominatorBudget delta sigma := add_le_add h.summation (sum_error _ _ _ h.exponential)

theorem denominator_positive (h : Stages exact approximate sum reciprocal output delta sigma rho tau)
    (lower : 1≤∑ i, exact i) (small : denominatorBudget delta sigma<1) :
    1-denominatorBudget delta sigma≤sum ∧ 0<sum := by
  have error := abs_le.mp (denominator_error h)
  constructor <;> linarith

/-- The exact stable row satisfies this from an attained maximum, not from a
hypothesis that the computed denominator happens to be positive. -/
theorem exact_denominator_bounds (exact : Fin n → ℝ) (nonneg : ∀ i, 0≤exact i)
    (upper : ∀ i, exact i≤1) (witness : ∃ i, exact i=1) :
    1≤∑ i, exact i ∧ (∑ i, exact i)≤n := by
  obtain ⟨i,hi⟩ := witness
  constructor
  · rw [← hi]; exact Finset.single_le_sum (fun j _ => nonneg j) (Finset.mem_univ i)
  · calc
      (∑ i, exact i) ≤ ∑ _i : Fin n, (1 : ℝ) := Finset.sum_le_sum (fun i _ => upper i)
      _ = n := by simp

/-- Perturb both numerator and denominator, with a derived positive lower bound. -/
theorem quotient_error (e u Z S delta D : ℝ)
    (nonneg : 0≤e) (upper : e≤1) (lower : 1≤Z)
    (numerator : |u-e|≤delta) (denominator : |S-Z|≤D) (small : D<1) :
    |u/S-e/Z|≤(delta+D)/(1-D) := by
  have dn : 0≤delta := (abs_nonneg _).trans numerator
  have Dn : 0≤D := (abs_nonneg _).trans denominator
  have Zpos : 0<Z := by linarith
  have margin : 0<1-D := by linarith
  have Sbound : 1-D≤S := by have := abs_le.mp denominator; linarith
  have Spos : 0<S := lt_of_lt_of_le margin Sbound
  have normalized : 0≤e/Z ∧ e/Z≤1 := ⟨div_nonneg nonneg (le_of_lt Zpos), (div_le_one Zpos).mpr (upper.trans lower)⟩
  have factor : |e/Z|≤1 := by rw [abs_of_nonneg normalized.1]; exact normalized.2
  have perturb : |(u-e)+(e/Z)*(Z-S)|≤delta+D := by
    calc
      _ ≤ |u-e|+|(e/Z)*(Z-S)| := abs_add_le _ _
      _ = |u-e|+|e/Z| * |S-Z| := by rw [abs_mul,abs_sub_comm Z S]
      _ ≤ delta+1*D := add_le_add numerator (mul_le_mul factor denominator (abs_nonneg _) (by norm_num))
      _ = delta+D := by ring
  have identity : u/S-e/Z=((u-e)+(e/Z)*(Z-S))/S := by
    field_simp [ne_of_gt Zpos, ne_of_gt Spos]; ring
  rw [identity,abs_div,abs_of_pos Spos]
  exact (div_le_div_of_nonneg_right perturb (le_of_lt Spos)).trans
    (div_le_div_of_nonneg_left (by linarith : 0≤delta+D) margin Sbound)

theorem coordinate_error (h : Stages exact approximate sum reciprocal output delta sigma rho tau)
    (nonneg : ∀ i, 0≤exact i) (upper : ∀ i, exact i≤1)
    (lower : 1≤∑ i, exact i) (small : denominatorBudget delta sigma<1) (i : Fin n) :
    |output i-exact i/(∑ j, exact j)|≤
      coordinateBudget (delta i) (denominatorBudget delta sigma) rho (tau i) := by
  have de := denominator_error h
  have q := quotient_error (exact i) (approximate i) (∑ j, exact j) sum (delta i)
    (denominatorBudget delta sigma) (nonneg i) (upper i) lower (h.exponential i) de small
  have mag : |approximate i|≤1+delta i := by
    calc
      |approximate i| = |exact i+(approximate i-exact i)| := by congr 1; ring
      _ ≤ |exact i|+|approximate i-exact i| := abs_add_le _ _
      _ ≤ 1+delta i := add_le_add (by rw [abs_of_nonneg (nonneg i)]; exact upper i) (h.exponential i)
  have dn : 0≤delta i := (abs_nonneg _).trans (h.exponential i)
  calc
    |output i-exact i/(∑ j, exact j)| =
      |(output i-approximate i*reciprocal)+approximate i*(reciprocal-1/sum)+
        (approximate i/sum-exact i/(∑ j, exact j))| := by congr 1; ring
    _ ≤ |output i-approximate i*reciprocal|+|approximate i*(reciprocal-1/sum)|+
        |approximate i/sum-exact i/(∑ j, exact j)| := (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ coordinateBudget (delta i) (denominatorBudget delta sigma) rho (tau i) := by
      unfold coordinateBudget
      rw [abs_mul]
      exact add_le_add (add_le_add (h.multiplication i)
        (mul_le_mul mag h.inverse (abs_nonneg _) (by linarith))) q

theorem normalization_error (h : Stages exact approximate sum reciprocal output delta sigma rho tau)
    (nonneg : ∀ i, 0≤exact i) (upper : ∀ i, exact i≤1)
    (lower : 1≤∑ i, exact i) (small : denominatorBudget delta sigma<1) :
    |(∑ i, output i)-1|≤∑ i, coordinateBudget (delta i) (denominatorBudget delta sigma) rho (tau i) := by
  have pos : 0<(∑ i, exact i) := by linarith
  have normalized : (∑ i, exact i/(∑ j, exact j))=1 := by
    rw [← Finset.sum_div]; exact div_self (ne_of_gt pos)
  rw [← normalized]
  exact sum_error _ _ _ (coordinate_error h nonneg upper lower small)

/-- Backward uses the computed forward weights and actual incoming sensitivities. -/
def dotBudget (pHat d epsilon eta : Fin n → ℝ) (sigma : ℝ) : ℝ :=
  sigma + ∑ i, (|d i| * epsilon i + |pHat i| * eta i)

structure BackwardStages (p pHat d dHat : Fin n → ℝ) (dot : ℝ)
    (difference gradient epsilon eta : Fin n → ℝ) (sigma : ℝ)
    (subError mulError : Fin n → ℝ) : Prop where
  weights : ∀ i, |pHat i-p i|≤epsilon i
  incoming : ∀ i, |dHat i-d i|≤eta i
  reduction : |dot-∑ i, pHat i*dHat i|≤sigma
  subtraction : ∀ i, |difference i-(dHat i-dot)|≤subError i
  multiplication : ∀ i, |gradient i-pHat i*difference i|≤mulError i

variable {p pHat d dHat difference gradient epsilon eta subError mulError : Fin n → ℝ}
  {dot : ℝ}

theorem backward_dot_error
    (h : BackwardStages p pHat d dHat dot difference gradient epsilon eta sigma subError mulError) :
    |dot-∑ i, p i*d i|≤dotBudget pHat d epsilon eta sigma := by
  have products (i : Fin n) :
      |pHat i*dHat i-p i*d i|≤|d i| * epsilon i+|pHat i| * eta i := by
    calc
      _ = |d i*(pHat i-p i)+pHat i*(dHat i-d i)| := by congr 1; ring
      _ ≤ |d i*(pHat i-p i)|+|pHat i*(dHat i-d i)| := abs_add_le _ _
      _ ≤ _ := by
        simp only [abs_mul]
        exact add_le_add (mul_le_mul_of_nonneg_left (h.weights i) (abs_nonneg _))
          (mul_le_mul_of_nonneg_left (h.incoming i) (abs_nonneg _))
  calc
    _ ≤ |dot-∑ i, pHat i*dHat i|+|(∑ i, pHat i*dHat i)-(∑ i, p i*d i)| := abs_sub_le _ _ _
    _ ≤ _ := add_le_add h.reduction (sum_error _ _ _ products)

def backwardBudget (pHat d p epsilon eta subError mulError : Fin n → ℝ)
    (sigma : ℝ) (i : Fin n) : ℝ :=
  mulError i + |d i-∑ j, p j*d j| * epsilon i +
    |pHat i| * (subError i+eta i+dotBudget pHat d epsilon eta sigma)

theorem backward_coordinate_error
    (h : BackwardStages p pHat d dHat dot difference gradient epsilon eta sigma subError mulError)
    (i : Fin n) :
    |gradient i-p i*(d i-∑ j, p j*d j)|≤
      backwardBudget pHat d p epsilon eta subError mulError sigma i := by
  have dotError := backward_dot_error h
  have subBound : |difference i-(d i-∑ j, p j*d j)|≤
      subError i+eta i+dotBudget pHat d epsilon eta sigma := by
    calc
      _ = |(difference i-(dHat i-dot))+(dHat i-d i)-
          (dot-∑ j, p j*d j)| := by congr 1; ring
      _ ≤ |difference i-(dHat i-dot)|+|dHat i-d i|+|dot-∑ j, p j*d j| :=
        (abs_sub _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
      _ ≤ _ := add_le_add (add_le_add (h.subtraction i) (h.incoming i)) dotError
  calc
    _ = |(gradient i-pHat i*difference i)+
        (d i-∑ j, p j*d j)*(pHat i-p i)+
        pHat i*(difference i-(d i-∑ j, p j*d j))| := by congr 1; ring
    _ ≤ |gradient i-pHat i*difference i|+
        |(d i-∑ j, p j*d j)*(pHat i-p i)|+
        |pHat i*(difference i-(d i-∑ j, p j*d j))| :=
      (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ _ := by
      simp only [abs_mul]
      exact add_le_add (add_le_add (h.multiplication i)
        (mul_le_mul_of_nonneg_left (h.weights i) (abs_nonneg _)))
        (mul_le_mul_of_nonneg_left subBound (abs_nonneg _))

/-- Real-arithmetic nonvacuity only: this is not encoded arithmetic or execution
existence. The witness supplies the actual intermediate operands. -/
theorem exact_stages (exact : Fin n → ℝ) :
    Stages exact exact (∑ i, exact i) (1/(∑ i, exact i))
      (fun i => exact i/(∑ j, exact j)) (fun _ => 0) 0 0 (fun _ => 0) := by
  constructor <;> intros <;> simp [div_eq_mul_inv]

theorem exact_backward_stages (p d : Fin n → ℝ) :
    BackwardStages p p d d (∑ i, p i*d i)
      (fun i => d i-∑ j, p j*d j) (fun i => p i*(d i-∑ j, p j*d j))
      (fun _ => 0) (fun _ => 0) 0 (fun _ => 0) (fun _ => 0) := by
  constructor <;> intros <;> simp

/-- Local error budgets do not imply a safe reciprocal without a smallness condition. -/
theorem denominator_can_be_zero :
    Stages (fun _ : Fin 1 => 1) (fun _ => 0) 0 0 (fun _ => 0) (fun _ => 1) 0 0 (fun _ => 0) := by
  constructor <;> intros <;> norm_num

end
end Ptx.Numerics.Softmax

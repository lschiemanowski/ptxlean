import PtxBinary32.SquareError

/-! Arithmetic of a separately chosen backward implementation. Every stage has
an explicit multiply and positive-zero add. Saved-forward provenance and actual
PTX execution belong to separate theorems. -/
namespace Ptx.Binary32.BackwardError
open TorchLean.Floats (eps32)
open FloatLib.Floats.Formats.BinaryInterchange (Model FloatFormat)

noncomputable def roundedProduct (lh rh : ℝ) : ℝ := SquareError.roundedAffine lh rh 0
noncomputable def roundedBase (ah dh : ℝ) : ℝ := roundedProduct (roundedProduct 2 dh) ah

def StageRange (lh rh : ℝ) : Prop :=
  |lh*rh| ≤ Bounds.maxFinite ∧ |lh*rh| + eps32 (lh*rh) ≤ Bounds.maxFinite

/-- All expressions refer to initial finite real input values, never actual
intermediate/output words whose finiteness is to be proved. -/
def Guards (xh wh ah dh : ℝ) : Prop :=
  StageRange 2 dh ∧ StageRange (roundedProduct 2 dh) ah ∧
    StageRange (roundedBase ah dh) wh ∧ StageRange (roundedBase ah dh) xh

noncomputable def stageBudget (lh rh l r el er : ℝ) : ℝ :=
  Error.affineBudget lh rh 0 l r el er 0
noncomputable def qBudget (dh d ed : ℝ) : ℝ := stageBudget 2 dh 2 d 0 ed
noncomputable def baseBudget (ah dh a d ea ed : ℝ) : ℝ :=
  stageBudget (roundedProduct 2 dh) ah (2*d) a (qBudget dh d ed) ea
noncomputable def parameterBudget (vh ah dh v a d ev ea ed : ℝ) : ℝ :=
  stageBudget (roundedBase ah dh) vh ((2*d)*a) v (baseBudget ah dh a d ea ed) ev

def Results (x w saved seed pQ q pDb db pDx dx pDw dw : Word) : Prop :=
  Error.AffineResults 0x40000000 seed 0 pQ q ∧
    Error.AffineResults q saved 0 pDb db ∧
    Error.AffineResults db w 0 pDx dx ∧ Error.AffineResults db x 0 pDw dw

/-- This literal has the actual finite binary32 meaning +2. -/
theorem two_real : finiteReal (0x40000000 : Word) = some 2 := by
  rw [finiteReal_some _ (by decide)]
  change some (Model.toReal (Model.ofFields FloatFormat.binary32 false 128 0)) = some 2
  rw [Model.toReal_ofFields_normal _ _ _ _ (by decide) (by decide) (by decide)]
  norm_num [FloatFormat.binary32, Model.pow2, FloatLib.Floats.Formats.Flocq.bpow,
    FloatLib.Numerics.binaryRadix, FloatLib.Numerics.Radix.toReal]

/-- A stage's rounded value and error are derived together from its two actual
instruction results and its input-range/error conditions. -/
theorem stage_error (left right product output : Word) (lh rh l r el er : ℝ)
    (leftReal : finiteReal left = some lh) (rightReal : finiteReal right = some rh)
    (range : StageRange lh rh) (leftError : |lh-l| ≤ el) (rightError : |rh-r| ≤ er)
    (allowed : Error.AffineResults left right 0 product output) :
    finiteReal output = some (roundedProduct lh rh) ∧
      |roundedProduct lh rh-l*r| ≤ stageBudget lh rh l r el er := by
  have real := SquareError.affine_value left right 0 product output lh rh 0
    leftReal rightReal SquareError.zero_real range.1 (by simpa using range.2) allowed
  obtain ⟨_, _, z, value, error⟩ := Error.affine_results left right 0 product output
    lh rh 0 l r 0 el er 0 leftReal rightReal SquareError.zero_real range.1
    (by simpa using range.2) leftError rightError (by simp) allowed
  have eq : z = roundedProduct lh rh := Option.some.inj (value.symm.trans real)
  exact ⟨real, by simpa [eq, stageBudget] using error⟩

/-- All permitted four-stage results have these finite interpretations and
absolute errors. The saved activation's error remains an explicit input promise. -/
theorem results_error (x w saved seed pQ q pDb db pDx dx pDw dw : Word)
    (xh wh ah dh idealX idealW idealA d ex ew ea ed : ℝ)
    (xReal : finiteReal x = some xh) (wReal : finiteReal w = some wh)
    (savedReal : finiteReal saved = some ah) (seedReal : finiteReal seed = some dh)
    (guards : Guards xh wh ah dh)
    (xError : |xh-idealX| ≤ ex) (wError : |wh-idealW| ≤ ew)
    (savedError : |ah-idealA| ≤ ea) (seedError : |dh-d| ≤ ed)
    (allowed : Results x w saved seed pQ q pDb db pDx dx pDw dw) :
    finiteReal q = some (roundedProduct 2 dh) ∧
    finiteReal db = some (roundedBase ah dh) ∧
    finiteReal dx = some (roundedProduct (roundedBase ah dh) wh) ∧
    finiteReal dw = some (roundedProduct (roundedBase ah dh) xh) ∧
    |roundedProduct (roundedBase ah dh) wh - 2*d*idealA*idealW| ≤
      parameterBudget wh ah dh idealW idealA d ew ea ed ∧
    |roundedProduct (roundedBase ah dh) xh - 2*d*idealA*idealX| ≤
      parameterBudget xh ah dh idealX idealA d ex ea ed ∧
    |roundedBase ah dh - 2*d*idealA| ≤ baseBudget ah dh idealA d ea ed := by
  obtain ⟨qReal, qError⟩ := stage_error 0x40000000 seed pQ q 2 dh 2 d 0 ed
    two_real seedReal guards.1 (by simp) seedError allowed.1
  obtain ⟨dbReal, dbError⟩ := stage_error q saved pDb db (roundedProduct 2 dh) ah
    (2*d) idealA (qBudget dh d ed) ea qReal savedReal guards.2.1 qError savedError allowed.2.1
  obtain ⟨dxReal, dxError⟩ := stage_error db w pDx dx (roundedBase ah dh) wh
    (2*d*idealA) idealW (baseBudget ah dh idealA d ea ed) ew
    dbReal wReal guards.2.2.1 dbError wError allowed.2.2.1
  obtain ⟨dwReal, dwError⟩ := stage_error db x pDw dw (roundedBase ah dh) xh
    (2*d*idealA) idealX (baseBudget ah dh idealA d ea ed) ex
    dbReal xReal guards.2.2.2 dbError xError allowed.2.2.2
  exact ⟨qReal, dbReal, dxReal, dwReal, dxError, dwError, dbError⟩

/-- Separate all-bit nonemptiness, with no finite numerical promises. -/
theorem results_exists (x w saved seed : Word) :
    ∃ pQ q pDb db pDx dx pDw dw, Results x w saved seed pQ q pDb db pDx dx pDw dw := by
  obtain ⟨pQ, hQ⟩ := Binary32.results_exists .mul 0x40000000 seed
  obtain ⟨q, hq⟩ := Binary32.results_exists .add pQ 0
  obtain ⟨pDb, hDb⟩ := Binary32.results_exists .mul q saved
  obtain ⟨db, hdb⟩ := Binary32.results_exists .add pDb 0
  obtain ⟨pDx, hDx⟩ := Binary32.results_exists .mul db w
  obtain ⟨dx, hdx⟩ := Binary32.results_exists .add pDx 0
  obtain ⟨pDw, hDw⟩ := Binary32.results_exists .mul db x
  obtain ⟨dw, hdw⟩ := Binary32.results_exists .add pDw 0
  exact ⟨pQ,q,pDb,db,pDx,dx,pDw,dw,⟨hQ,hq⟩,⟨hDb,hdb⟩,⟨hDx,hdx⟩,hDw,hdw⟩
end Ptx.Binary32.BackwardError

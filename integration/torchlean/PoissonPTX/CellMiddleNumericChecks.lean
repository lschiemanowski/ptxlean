import PoissonPTX.CellMiddleCorrespondence
import PoissonPTX.CellMiddleWitness
import PoissonPTX.ZeroSources

/-! A completed concrete source-constrained Q1 witness and code mutations.
The source constraints remain weaker than complete PTX memory admission. -/
namespace PtxTorchLean.Poisson.PTX.Concurrent.CellMiddle.Numeric.Checks
open Ptx Symbolic
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

-- Keep elaboration from unfolding the complete interpreter result while
-- inferring implicit event-list arguments; its proved equations remain available.
attribute [local irreducible] Witness.result

def launch : Launch 2 (fun _ => 0) Witness.start := {
  generation:=0, reset:=rfl, pcs:=by intro t; rfl,
  global:=by intro t; simp [Witness.start,Witness.seed],
  shared:=by intro t; simp [Witness.start,Witness.seed],
  lanes:=by intro t; simp [Witness.start,Witness.seed],
  rows:=by intro t; simp [Witness.start,Witness.seed],
  cols:=by intro t; simp [Witness.start,Witness.seed],
  fits:=by decide }

theorem decode_zero (w : Word) (h : decode w=decode 0) : w=0 := by
  have bits := congrArg (fun x : Float => x.toBits.toBitVec) h
  change Float.Model.UnpackedFloat.pack Float.Model.Format.binary64
    (Float.Model.UnpackedFloat.unpack Float.Model.Format.binary64 w)=0 at bits
  rw [FloatLib.Floats.Formats.BinaryInterchange.Model.pack_unpack_eq] at bits
  split at bits
  · have ne : Float.Model.UnpackedFloat.packedNaN Float.Model.Format.binary64≠(0:Word) := by decide +kernel
    exact False.elim (ne bits)
  · exact bits

/-- This finite check evaluates only the small symbolic arithmetic expression. -/
theorem expected_zero : ∀ (plane : Fin 7) (lane : Fin 4),
    (expected 2 plane.val lane.val).eval (fun _ => 0) (fun _ _ => 0)=decode 0 := by decide +kernel

theorem zero_words : ZeroSources.Zero Witness.result.events := by
  intro thread access member
  have reads : Symbolic.Reads (fun _ _ => 0) Witness.result.events :=
    ZeroSources.execute_zero_reads Witness.executed
  cases write : access.data.store with
  | false => exact reads thread access member write
  | true =>
    obtain ⟨index,observed⟩ := List.mem_iff_getElem?.mp member
    have shared := Inputs.store_space Witness.candidate_run (Inputs.shared_stores 2 (by decide) (by decide)) member write
    obtain ⟨p,active,pc,address⟩ := CellMiddle.Checks.coverage 2 (by decide) (by decide)
      Witness.candidate_run launch.reset launch.pcs launch.base_nat launch.lane_nat launch.fits index thread access observed write shared
    have positive := Inputs.nonzero_plane 2 Witness.candidate_run member write pc
    have value := store_expression_of_reads launch (by decide) (by decide) Witness.candidate_run reads member write p positive pc
    apply decode_zero
    exact value.trans (expected_zero p ⟨thread.val,active⟩)

theorem compatible : Visibility.Compatible (fun _ _ => 0) Witness.result.events (ZeroSources.source Witness.result.events) :=
  ZeroSources.compatible zero_words

theorem performed : Visibility.Performed Witness.result.events (ZeroSources.source Witness.result.events) :=
  ZeroSources.performed Witness.candidate_run

/-- The completed-execution theorem has an actual witness satisfying both
source constraints, all three barriers and all 32 participants. -/
theorem witness_correspondence (plane : Fin 7) (positive : plane≠0) :
    grid 2 (fun _ => 0) (view 2 (fun _ => 0) (fun _ _ => 0) Witness.result.events) .shared (plane.val*2*2*8)=
      Correspondence.entries (target
        (initialTensor 2 (fun _ => 0) (fun _ _ => 0) .global 0)
        (initialTensor 2 (fun _ => 0) (fun _ _ => 0) .global 64)
        (initialTensor 2 (fun _ => 0) (fun _ _ => 0) .global 128)
        (initialTensor 2 (fun _ => 0) (fun _ _ => 0) .shared 0) plane.val) :=
  completed_middle launch (by decide) (by decide) Witness.candidate_run Witness.finished.2 compatible performed plane positive

/-- Retaining the index within a valid plane is insufficient: changing the
matrix coordinate must also fail the numerical certificate. -/
theorem wrong_coordinate_rejected :
    number (atPC .values ((CellMiddle.Checks.program 2).set 12
      (.data (.load64 .shared 5 (.offset 2 8)))) (seed 2 0)
      (site (CellMiddle.Checks.program 2) 2 1) 8)≠some (expected 2 1 0) := by decide +kernel

/-- Addition in place of the integration-weight multiplication is rejected. -/
theorem wrong_weight_rejected :
    number (atPC .values ((CellMiddle.Checks.program 2).set
      (site (CellMiddle.Checks.program 2) 2 3-3) (.data (.fp .add 8 (.reg 8) (.reg 6))))
      (seed 2 0) (site (CellMiddle.Checks.program 2) 2 3) 8)≠some (expected 2 3 0) := by decide +kernel

end PtxTorchLean.Poisson.PTX.Concurrent.CellMiddle.Numeric.Checks

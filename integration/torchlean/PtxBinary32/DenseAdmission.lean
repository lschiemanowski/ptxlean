import PtxBinary32.DenseReplay
import PtxBinary32.ParallelAdmission

/-! A complete admitted selected dense-forward execution, with actual stored
outputs and conditional numerical bounds. This is existence in the restricted
memory model, not universal correctness, fairness or hardware conformance. -/
namespace Ptx.Scalar.Parallel.Dense

/-- Admission, termination, output words and safety concern the same complete
instruction trace. Memory validity is proved, not a caller assumption. -/
theorem selected_forward_admitted (s : Shape) (b : Bounds s) (global shared : List Word)
    (seeds : Fin s.threads → Scalar.State)
    (globalBound : s.globalWords ≤ global.length) (sharedBound : s.sharedWords ≤ shared.length) :
    ∃ events final, ∃ run : ConcreteRuns (config s b) (program s) (initial s global shared seeds) events final,
      ∃ source co,
      Graph.Ordered.Valid (Memory.graph (program s) global shared events source co)
        (Memory.runOrder run.toRuns (show (initial s global shared seeds).barrier = Barrier.reset 0 from rfl) source co).cross ∧
      (∀ i, ¬Path (SharedReduction.Machine.Memory.grounding
        (Memory.graph (program s) global shared events source co)
        (Memory.runOrder run.toRuns (show (initial s global shared seeds).barrier = Barrier.reset 0 from rfl) source co).cross) i i) ∧
      (∀ t, (final.lanes t).halted = true ∧ (final.lanes t).scalar.pc = (program s).length-1) ∧
      (∀ r, r<s.rows → final.global[s.outputBase+r]? = some (forwardWord s global r)) ∧
      (∀ i, i<s.outputBase → final.global[i]? = global[i]?) ∧
      final.global.length = global.length ∧ final.shared.length = shared.length ∧
      final.barrier = Barrier.reset (s.depth+1) ∧ final.site = none ∧
      (∀ event ∈ events, AccessSafe (initial s global shared seeds) event) ∧
      (∀ r, r<s.rows → ∀ i : Ptx.Binary32.Reduction.RowInput,
        Ptx.Binary32.Reduction.words i.tree =
          Ptx.Binary32.Reduction.balanced s.depth 0 (operands s global r) →
        i.bias = global[s.biasBase+r]! →
        Ptx.Binary32.finiteReal final.global[s.outputBase+r]! = some (max i.affine 0) ∧
          |max i.affine 0-max i.idealAffine 0| ≤ i.error) := by
  obtain ⟨events,final,run,done,values,inputs,gl,sl,barrier,site,safe⟩ :=
    selected_forward_concrete s b global shared seeds globalBound sharedBound
  obtain ⟨source,co,valid,grounded⟩ := Memory.Chronology.concrete_admitted run
    (show (initial s global shared seeds).barrier = Barrier.reset 0 from rfl)
  refine ⟨events,final,run,source,co,valid,grounded,done,values,inputs,gl,sl,barrier,site,safe,?_⟩
  intro r hr i tree bias
  rw [List.getElem!_eq_getElem?_getD,values r hr]
  exact forward_accuracy s global r i tree bias

end Ptx.Scalar.Parallel.Dense

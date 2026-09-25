import PtxBinary32.DenseForward
import PtxBinary32.ParallelReplaySources

/-! The complete selected dense forward trace has checked chronological read
origins. This is evidence for constructing a memory graph, not a proof of its
admission under the PTX memory constraints. -/
namespace Ptx.Scalar.Parallel.Dense

/-- Preserve all complete-forward guarantees while exposing the exact replay
and source evidence. No desired load value is supplied as a premise. -/
theorem selected_forward_checked (s : Shape) (b : Bounds s) (global shared : List Word)
    (seeds : Fin s.threads → Scalar.State)
    (globalBound : s.globalWords ≤ global.length) (sharedBound : s.sharedWords ≤ shared.length) :
    ∃ events final, ConcreteRuns (config s b) (program s) (initial s global shared seeds) events final ∧
      Replay.trace ⟨global,shared⟩ events = some (Replay.arrays final) ∧
      Replay.ReadOrigins ⟨global,shared⟩ events ∧
      (∀ t, (final.lanes t).halted = true ∧ (final.lanes t).scalar.pc = (program s).length-1) ∧
      (∀ r, r<s.rows → final.global[s.outputBase+r]? = some (forwardWord s global r)) ∧
      (∀ i, i<s.outputBase → final.global[i]? = global[i]?) ∧
      final.global.length = global.length ∧ final.shared.length = shared.length ∧
      final.barrier = Barrier.reset (s.depth+1) ∧ final.site = none ∧
      (∀ event ∈ events, AccessSafe (initial s global shared seeds) event) := by
  obtain ⟨events,final,run,rest⟩ := selected_forward_concrete s b global shared seeds globalBound sharedBound
  have replay := Replay.concrete_replays run
  exact ⟨events,final,run,replay,Replay.read_origins replay,rest⟩

end Ptx.Scalar.Parallel.Dense

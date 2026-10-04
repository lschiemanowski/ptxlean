import PoissonPTX.ObservedRoundedHistory
import PoissonPTX.ObservedRoundedProjectSources

namespace PtxTorchLean.Poisson.PTX.Rounded
open Flow.Parallel Concurrent

/-- In every completed rounded launch, recovering the active histories loses
no records at all. Padding has no memory observations by its actual guard. -/
theorem history {start final : Fin (count n) → Flow.State}
    (small : n<2^30)
    (run : Flow.Parallel.Runs (context base) (VectorFlowEntry.program (BitVec.ofNat 32 n) body)
      start words indices final)
    (pcs : ∀ t, (start t).core.pc=0) (running : ∀ t, (start t).halted=false)
    (done : ∀ t, (final t).halted=true) :
    (words.filterMap (restrictEvent n)).map (renameEvent (Fin.castLE enough))=words ∧
      (indices.filterMap (restrictIndex n)).map (fun (owner,a) => (owner.castLE enough,a))=indices := by
  have active := vector_active_records (n:=n) run pcs running done
    (by intro t padding; rw [live base small]; omega)
  exact ⟨recover_words enough words active.1 (no_barriers run),recover_indices enough indices active.2⟩

end PtxTorchLean.Poisson.PTX.Rounded

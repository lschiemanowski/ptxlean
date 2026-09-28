import PtxBinary32.UnaryPointwiseStored
import PtxBinary32.UnaryPointwiseData
import PtxBinary32.UnaryPointwiseCoverage
import PtxBinary32.UnaryPointwiseExecution
import PtxBinary32.ParallelUnaryAdmission

/-! A parallel unary launch is a fetched, completed, memory-admitted execution.
The stored-result specification is derived from it, never a launch premise.
Conversely every allowed vector result has a constructive admitted execution. -/
namespace Ptx.Scalar.UnaryPointwise
open ParallelUnary

/-- Actual launch with arbitrary candidate loads and one common fetched program.
The bounds describe allocated global memory and the read-only common cell. -/
inductive Launch (op : Op) (n common : Nat) (before after : List Word) : Prop
  | execution (bounds : Bounds n common before)
      (seeds : Fin n → Scalar.State) (events : List (ParallelUnary.Event n))
      (final : ParallelUnary.State n)
      (run : ParallelUnary.Runs target (program op) (initial common before seeds) events final)
      (halted : ∀t, (final.lanes t).halted=true)
      (source co) (admitted : Memory.Admitted (program op) before events source co)
      (output : final.global=after) : Launch op n common before after

theorem launch_bounds (launch : Launch op n common before after) : Bounds n common before := by
  cases launch with
  | execution bounds => exact bounds

/-- Every completed admitted execution stores the specified arithmetic relation
for every thread and preserves the rest of the memory arena. -/
theorem launch_spec (launch : Launch op n common before after) : Spec op n common before after := by
  cases launch with
  | execution bounds seeds events final run halted source co admitted output =>
    subst after
    have fit : common<2^62 := bounds.2.2.2.1.trans bounds.2.2.2.2
    refine ⟨ParallelUnary.runs_length run,?_,?_⟩
    · intro j outside
      apply ParallelUnary.runs_frame run
      intro event member effect memory store equal
      rcases run_memory run member memory with ⟨_,bad,_⟩|⟨_,bad,_⟩|⟨_,_,address⟩ <;>
        try {rw [store] at bad; contradiction}
      rw [address,pointer_index event.thread.val (by have := event.thread.isLt; omega)] at equal
      have := event.thread.isLt
      omega
    · intro t
      obtain ⟨event,effect,member,thread,memory,store⟩ := completed_store run t (halted t)
      have value := stored_final run fit bounds.2.2.1 member memory store
      have correct := store_results run bounds source co admitted member memory store
      rw [thread] at value correct
      have read : final.global[t.val]! = effect.value := by
        simp [List.getElem!_eq_getElem?_getD,value]
      rw [read]
      exact correct

/-- Every memory effect of the exact execution underlying a launch is aligned
and inside its original allocation. -/
theorem launch_safe (launch : Launch op n common before after) :
    ∃(seeds : Fin n → Scalar.State) (events : List (ParallelUnary.Event n)) (final : ParallelUnary.State n),
      ParallelUnary.Runs target (program op) (initial common before seeds) events final ∧
      final.global=after ∧ (∀t,(final.lanes t).halted=true) ∧
      (∃source co,Memory.Admitted (program op) before events source co) ∧
      ∀event∈events,∀effect,event.memory=some effect → Scalar.ValidAddress before effect.address := by
  cases launch with
  | execution bounds seeds events final run halted source co admitted output =>
    exact ⟨seeds,events,final,run,output,halted,⟨source,co,admitted⟩,
      fun event member effect memory => ParallelUnary.runs_memory_safe run member memory⟩

/-- Existence chooses a legal schedule and constructs actual read sources and
coherence. Universal correctness above still covers every admitted schedule. -/
theorem launch_realize (op : Op) (n common : Nat) (before after : List Word)
    (bounds : Bounds n common before) (spec : Spec op n common before after) :
    Launch op n common before after := by
  obtain ⟨seeds,events,final,run,output,halted,reads⟩ := realize op n common before after bounds spec
  have initialReads : Memory.Chronology.InitialReads before events := initial_reads_bounded run reads
  have future : Memory.Chronology.FutureStores events := by
    intro p q e f a b hp hq ha hb read store same
    exact (stores_follow_read run.toRuns bounds.2.2.1
      (bounds.2.2.2.1.trans bounds.2.2.2.2) p q e f a b hp hq ha hb read store same).2
  obtain ⟨source,co,admitted,_⟩ := Memory.Chronology.admitted_of_initial_reads
    (program:=program op) initialReads future
  exact .execution bounds seeds events final run.toRuns halted source co admitted output

end Ptx.Scalar.UnaryPointwise

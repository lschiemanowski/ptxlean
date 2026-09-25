import PtxBinary32.ParallelCompletion
import PtxBinary32.ParallelMemory

/-! Derive both sides of barrier timing from actual instruction sites. The
unique-address writer obligation remains explicit until a kernel discharges it. -/
namespace Ptx.Scalar.Parallel.Memory

/-- The old visibility rule with its dynamic timing premises discharged by
straight-line instruction order and the observed barrier completion. The kernel
still supplies actual issuing-site evidence and unique location ownership. -/
theorem run_read_from_unique_writer_sites {cfg : Config n} {s final : State n} {events : List (Event n)}
    (run : Runs cfg program s events final) (reset : s.barrier=Barrier.reset generation)
    (straight : Control.Straight program) (source co) (phase : History.Phase events)
    (w r : Fin (labels program s.global s.shared events).length) (writer reader : Fin n)
    (valid : Graph.Ordered.Valid (graph program s.global s.shared events source co) (runOrder run reset source co).cross)
    (wo : owner n ((graph program s.global s.shared events source co).event w)=some writer)
    (ro : owner n ((graph program s.global s.shared events source co).event r)=some reader)
    (producer : ∃ space occ, events[((graph program s.global s.shared events source co).event w).position]? =
      some (.scalar writer space occ) ∧ occ.pc<phase.key.site)
    (consumer : ∃ space occ, events[((graph program s.global s.shared events source co).event r).position]? =
      some (.scalar reader space occ) ∧ phase.key.site<occ.pc)
    (written : (graph program s.global s.shared events source co).write w)
    (read : (graph program s.global s.shared events source co).read r)
    (same : (graph program s.global s.shared events source co).sameAddress w r)
    (unique : ∀ v, (graph program s.global s.shared events source co).write v →
      (graph program s.global s.shared events source co).sameAddress v r →
      ¬(graph program s.global s.shared events source co).initial v → v=w) :
    (graph program s.global s.shared events source co).source r=w ∧
      ((graph program s.global s.shared events source co).event r).effect.value =
      ((graph program s.global s.shared events source co).event w).effect.value := by
  obtain ⟨wspace,wocc,atW,wsite⟩ := producer
  obtain ⟨rspace,rocc,atR,rsite⟩ := consumer
  have aligned : Aligned s := by intro t ht; simp [reset,Barrier.reset] at ht
  have arrival := History.arrival_position_spec (History.completed_arrivals run reset) phase writer
  have before := (Control.position_iff_pc run straight _ _ _ _ writer wocc.pc phase.key.site
    atW arrival.2 rfl rfl).mpr wsite
  have after := Control.site_after_completion run straight aligned phase.position _ phase.key
    _ reader rocc.pc phase.observed atR rfl rsite
  exact run_read_from_unique_writer run reset source co phase w r writer reader valid wo ro
    before after written read same unique

end Ptx.Scalar.Parallel.Memory

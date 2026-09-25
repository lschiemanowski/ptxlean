import PtxBinary32.ParallelSources

/-! A sufficient admitted witness for concrete-read executions. All graph
sources, chronological write order and actual barrier-order obligations are
proved. This does not require general candidates to use concrete reads. -/
namespace Ptx.Scalar.Parallel.Memory.Chronology
variable {n : Nat} {events : List (Event n)} {program : List Instr}
  {cfg : Config n} {start final : State n}

noncomputable def chosenSource (run : ConcreteRuns cfg program start events final)
    (r : Fin (labels program start.global start.shared events).length) :
    Fin (labels program start.global start.shared events).length :=
  if h : (graph program start.global start.shared events id (fun _ _ => false)).read r
  then Classical.choose (source_exists run r h) else r

noncomputable def chronologicalCoherence (program : List Instr) (global shared : List Word)
    (events : List (Event n)) (a b : Fin (labels program global shared events).length) : Bool := by
  classical
  let g := graph program global shared events id (fun _ _ => false)
  exact decide (g.write a ∧ g.write b ∧ g.sameAddress a b ∧ rank global shared (g.event a)<rank global shared (g.event b))

theorem chosenSource_spec (run : ConcreteRuns cfg program start events final)
    (r : Fin (labels program start.global start.shared events).length)
    (read : (graph program start.global start.shared events id (fun _ _ => false)).read r) :
    SourceFor program start.global start.shared events r (chosenSource run r) := by
  rw [chosenSource,dite_eq_left read]
  exact Classical.choose_spec (source_exists run r read)

/-- The existing serial certificate is derived from actual fetched execution,
including its reset-barrier history. No memory-admission premise is supplied. -/
theorem concrete_certificate (run : ConcreteRuns cfg program start events final)
    (reset : start.barrier = Barrier.reset generation) :
    SharedReduction.Machine.Memory.SerialCertificate
      (graph program start.global start.shared events (chosenSource run)
        (chronologicalCoherence program start.global start.shared events))
      (runOrder run.toRuns reset (chosenSource run)
        (chronologicalCoherence program start.global start.shared events)).cross
      (fun i => rank start.global start.shared (labels program start.global start.shared events)[i.val]) := by
  classical
  let g := graph program start.global start.shared events (chosenSource run)
    (chronologicalCoherence program start.global start.shared events)
  have spec : ∀ r, g.read r → SourceFor program start.global start.shared events r (g.source r) :=
    fun r read => chosenSource_spec run r read
  refine {
    injective := rank_injective program start.global start.shared events
    sources := ⟨fun r read => ⟨(spec r read).1,(spec r read).2.1,(spec r read).2.2.1⟩⟩
    source_before := fun r read => (spec r read).2.2.2.1
    latest := fun w r write read same before => (spec r read).2.2.2.2 w write same before
    coherence_iff := ?_
    initial_before := ?_
    base_before := ?_
  }
  · intro a b
    change chronologicalCoherence program start.global start.shared events a b = true ↔ _
    unfold chronologicalCoherence
    exact @decide_eq_true_iff _ _
  · intro i w hi _ same ne
    exact initial_before program start.global start.shared events (chosenSource run)
      (chronologicalCoherence program start.global start.shared events) i w hi same ne
  · intro a b edge
    exact base_before program start.global start.shared events (History.completed_arrivals run.toRuns reset)
      (chosenSource run) (chronologicalCoherence program start.global start.shared events) a b edge

/-- A concrete-read execution starting at a reset barrier has an admitted graph
on exactly its emitted labels. The same certificate excludes circular chains
through actual base edges and read-source edges. -/
theorem concrete_admitted (run : ConcreteRuns cfg program start events final)
    (reset : start.barrier = Barrier.reset generation) :
    ∃ source co,
      Graph.Ordered.Valid (graph program start.global start.shared events source co)
        (runOrder run.toRuns reset source co).cross ∧
      ∀ i, ¬Path (SharedReduction.Machine.Memory.grounding
        (graph program start.global start.shared events source co)
        (runOrder run.toRuns reset source co).cross) i i := by
  let cert := concrete_certificate run reset
  exact ⟨chosenSource run,chronologicalCoherence program start.global start.shared events,cert.valid,cert.grounded⟩

end Ptx.Scalar.Parallel.Memory.Chronology

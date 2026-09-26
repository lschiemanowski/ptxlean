import PtxBinary32.GridSources

/-! A sufficient admitted witness for concrete-read executions. All graph
sources, chronological write order and actual barrier-order obligations are
proved. This does not require general candidates to use concrete reads. -/
namespace Ptx.Scalar.Parallel.Grid.Memory.Chronology
variable {groups n : Nat} {events : List (Grid.Event groups n)} {program : List Instr}
  {cfg : Config n} {start final : Grid.State groups n}

noncomputable def chosenSource (run : Grid.ConcreteRuns cfg program start events final)
    (r : Fin (labels program start events).length) :
    Fin (labels program start events).length :=
  if h : (graph program start events id (fun _ _ => false)).read r
  then Classical.choose (source_exists run r h) else r

noncomputable def chronologicalCoherence (program : List Instr) (start : Grid.State groups n)
    (events : List (Grid.Event groups n)) (a b : Fin (labels program start events).length) : Bool := by
  classical
  let g := graph program start events id (fun _ _ => false)
  exact decide (g.write a ∧ g.write b ∧ g.sameAddress a b ∧ rank start (g.event a)<rank start (g.event b))

theorem chosenSource_spec (run : Grid.ConcreteRuns cfg program start events final)
    (r : Fin (labels program start events).length)
    (read : (graph program start events id (fun _ _ => false)).read r) :
    SourceFor program start events r (chosenSource run r) := by
  rw [chosenSource,dite_eq_left read]
  exact Classical.choose_spec (source_exists run r read)

/-- The existing serial certificate is derived from actual fetched execution,
including all actual within-group barrier edges. No memory-admission premise is supplied. -/
theorem concrete_certificate (run : Grid.ConcreteRuns cfg program start events final) :
    SharedReduction.Machine.Memory.SerialCertificate
      (graph program start events (chosenSource run)
        (chronologicalCoherence program start events))
      (cross program start events)
      (fun i => rank start (labels program start events)[i.val]) := by
  classical
  let g := graph program start events (chosenSource run)
    (chronologicalCoherence program start events)
  have spec : ∀ r, g.read r → SourceFor program start events r (g.source r) :=
    fun r read => chosenSource_spec run r read
  refine {
    injective := rank_injective program start events
    sources := ⟨fun r read => ⟨(spec r read).1,(spec r read).2.1,(spec r read).2.2.1⟩⟩
    source_before := fun r read => (spec r read).2.2.2.1
    latest := fun w r write read same before => (spec r read).2.2.2.2 w write same before
    coherence_iff := ?_
    initial_before := ?_
    base_before := ?_
  }
  · intro a b
    change chronologicalCoherence program start events a b = true ↔ _
    unfold chronologicalCoherence
    exact @decide_eq_true_iff _ _
  · intro i w hi _ same ne
    exact initial_before program start events (chosenSource run)
      (chronologicalCoherence program start events) i w hi same ne
  · intro a b edge
    exact base_before program start events (chosenSource run) (chronologicalCoherence program start events) a b edge

/-- A concrete-read grid execution has an admitted graph
on exactly its emitted labels. The same certificate excludes circular chains
through actual base edges and read-source edges. -/
theorem concrete_admitted (run : Grid.ConcreteRuns cfg program start events final) :
    ∃ source co,
      Graph.Ordered.Valid (graph program start events source co)
        (cross program start events) ∧
      ∀ i, ¬Path (SharedReduction.Machine.Memory.grounding
        (graph program start events source co)
        (cross program start events)) i i := by
  let cert := concrete_certificate run
  exact ⟨chosenSource run,chronologicalCoherence program start events,cert.valid,cert.grounded⟩

/-- The public admission predicate follows without assuming any desired output. -/
theorem concrete_admitted_exists (run : Grid.ConcreteRuns cfg program start events final) :
    Memory.Admitted program start events := by
  obtain ⟨source,co,valid,_⟩ := concrete_admitted run
  exact ⟨source,co,valid⟩

end Ptx.Scalar.Parallel.Grid.Memory.Chronology

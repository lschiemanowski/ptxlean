import PtxBinary32.DenseDataMachine
import PtxBinary32.DenseReadData

namespace Ptx.Scalar.Parallel.Dense

/-- Every actual stored value in a completed admitted candidate execution is
justified by its fetched arithmetic. Loads are proved from past stores and
initialization, rather than supplied as an arithmetic-correctness assumption. -/
theorem run_data (s : Shape) (b : Bounds s) (global shared : List Word)
    (seeds : Fin s.threads → Scalar.State) {events : List (Event s.threads)} {final : Parallel.State s.threads}
    (run : Runs (config s b) (program s) (initial s global shared seeds) events final)
    (halted : ∀ t, (final.lanes t).halted=true) (source co) (valid : Admitted s b global shared seeds run source co) :
    DataInvariant s global final ∧ Stores s global events := by
  have aux (current : Parallel.State s.threads) (rest : List (Event s.threads))
      (tail : Runs (config s b) (program s) current rest final) :
      ∀ before, events=before++rest →
      Runs (config s b) (program s) (initial s global shared seeds) before current →
      DataInvariant s global current → Stores s global before →
      DataInvariant s global final ∧ Stores s global events := by
    induction tail with
    | nil =>
      intro before split prefixRun inv past
      simpa [split] using And.intro inv past
    | @cons candidate t state out rest finish step tail ih =>
      intro before split prefixRun inv past
      have reads : Reads s global out.events := by
        intro reader space occ effect member memory load
        have singleton := scalar_step_singleton step member
        have atQ : events[before.length]?=some (.scalar reader (some space) occ) := by
          rw [split,singleton]
          simp
        apply read_data s b global shared seeds run halted source co valid before.length reader space occ effect atQ memory load
        intro p hp writer so stored atP sm sk
        have inBefore : before[p]?=some (.scalar writer (some .shared) so) := by
          simpa [split,List.getElem?_append,hp] using atP
        exact past writer .shared so stored (List.mem_of_getElem? inBefore) sm sk
      have aligned := runs_aligned prefixRun (reset_aligned _ _ _ _)
      obtain ⟨nextInv,newStores⟩ := step_data s b global step inv aligned reads
      have allStores : Stores s global (before++out.events) := by
        intro owner space occ effect member memory store
        rcases List.mem_append.mp member with old | new
        · exact past owner space occ effect old memory store
        · exact newStores owner space occ effect new memory store
      exact ih run halted valid (before++out.events) (by simpa [List.append_assoc] using split)
        (runs_append prefixRun (by simpa using Runs.cons step Runs.nil)) nextInv allStores
  exact aux _ _ run [] (by simp) .nil (fun t => initial_data s global shared seeds t)
    (by intro _ _ _ _ member; simp at member)

end Ptx.Scalar.Parallel.Dense

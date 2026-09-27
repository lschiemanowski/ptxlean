import PtxBinary32.SumProgram

/-! The actual fetched sum inherits the previously proved memory observations,
termination witness and universal correspondence of its dense specialization. -/
namespace Ptx.Scalar.Parallel.Sum

abbrev config (d : Nat) (bound : Bounds d) := Dense.config (shape d) (denseBounds d bound)

abbrev initial (d : Nat) (input : Fin (width d) → Word) (shared : List Word)
    (seeds : Fin (shape d).threads → Scalar.State) :=
  Dense.initial (shape d) (global d input) shared seeds

/-- Every completed admitted candidate run stores the ordered arithmetic sum.
The memory graph's validity is the existing semantic admission condition;
input preservation and actual emitted-access safety are conclusions. -/
theorem completed (d : Nat) (bound : Bounds d) (input : Fin (width d) → Word)
    (shared : List Word) (seeds : Fin (shape d).threads → Scalar.State)
    {events : List (Event (shape d).threads)} {final : State (shape d).threads}
    (run : Runs (config d bound) (program d) (initial d input shared seeds) events final)
    (halted : ∀ t, (final.lanes t).halted=true)
    (source co) (valid : Dense.Admitted (shape d) (denseBounds d bound)
      (global d input) shared seeds run source co) :
    (∃ value, final.global[outputIndex d]?=some value ∧ Output d input value) ∧
    (∀ j : Fin (width d), final.global[j.val]?=some (input j)) ∧
    (∀ i, i<outputIndex d → final.global[i]?=(global d input)[i]?) ∧
    final.global.length=(global d input).length ∧ final.shared.length=shared.length ∧
    (∀ event ∈ events, AccessSafe (initial d input shared seeds) event) := by
  have result := Dense.completed_forward (shape d) (denseBounds d bound) (global d input)
    shared seeds run halted source co valid
  obtain ⟨value,stored,allowed⟩ := result.1 ⟨0,by simp [shape]⟩
  refine ⟨⟨value,?_,(output_iff d input value).mp allowed⟩,?_,?_,result.2.2.1,result.2.2.2.1,result.2.2.2.2⟩
  · simpa using stored
  · intro j
    rw [result.2.1 j.val (by rw [outputBase_eq]; unfold outputIndex; omega)]
    exact global_input d input j
  · intro i hi
    exact result.2.1 i (by simpa using hi)

/-- A complete concrete run exists with memory admission proved from its
actual trace. No fairness, hardware-launch or GPU-performance claim is made. -/
theorem exists_admitted (d : Nat) (bound : Bounds d) (input : Fin (width d) → Word)
    (shared : List Word) (seeds : Fin (shape d).threads → Scalar.State)
    (allocated : sharedWords d≤shared.length) :
    ∃ events final, ∃ run : ConcreteRuns (config d bound) (program d)
        (initial d input shared seeds) events final,
      (∃ source co, Dense.Admitted (shape d) (denseBounds d bound)
        (global d input) shared seeds run.toRuns source co) ∧
      (∀ t, (final.lanes t).halted=true ∧ (final.lanes t).scalar.pc=(program d).length-1) ∧
      (∃ value, final.global[outputIndex d]?=some value ∧ Output d input value) ∧
      (∀ j : Fin (width d), final.global[j.val]?=some (input j)) ∧
      (∀ i, i<outputIndex d → final.global[i]?=(global d input)[i]?) ∧
      final.global.length=(global d input).length ∧ final.shared.length=shared.length ∧
      final.barrier=Barrier.reset (d+1) ∧ final.site=none ∧
      (∀ event ∈ events, AccessSafe (initial d input shared seeds) event) := by
  obtain ⟨events,final,run,source,co,valid,_,halted,_,_,gl,sl,barrier,site,safe,_⟩ :=
    Dense.selected_forward_admitted (shape d) (denseBounds d bound) (global d input)
      shared seeds (by simp) (by simpa using allocated)
  have output := completed d bound input shared seeds run.toRuns (fun t => (halted t).1) source co valid
  exact ⟨events,final,run,⟨source,co,valid⟩,halted,output.1,output.2.1,output.2.2.1,
    gl,sl,barrier,site,safe⟩

end Ptx.Scalar.Parallel.Sum

import PoissonPTX.DotTreeOwnership
import PoissonPTX.NativeFlowProducer
import PoissonPTX.DotBarriers

namespace PtxTorchLean.Poisson.PTX.Concurrent.Dot

def storeAddress (phase : Fin 9) : Operand := if phase.val=0 then .offset 2 0 else .reg 2

theorem checked_store_fetch : ∀ phase : Fin 9,
    Reduction.Native.code[2+9*phase.val]?=some (.data (.store64 .shared (storeAddress phase) (.reg 8))) := by decide +kernel

theorem store_fetch (phase : Fin 9) :
    (program count left right output scratch)[storeSite phase]?=
      some (.flow (.data (.data (.store64 .shared (storeAddress phase) (.reg 8))))) := by
  have inside : 2+9*phase.val<76 := by have := phase.isLt; omega
  have position : storeSite phase=20+(2+9*phase.val) := by simp [storeSite]; omega
  rw [position,tree_fetch inside,checked_store_fetch]
  rfl

theorem checked_store_protection : ∀ (phase : Fin 9) (slot : Fin 76),
    (match Reduction.Native.code[slot.val]? with
    | some (.branch target) => decide (20+slot.val<storeSite phase → storeSite phase<20+target →
        ∃ count : Fin 257, treeGuard (20+slot.val)=some count.val ∧ Reduction.active phase≤count.val)
    | _ => true)=true := by decide +kernel

/-- An active lane cannot take a branch that skips this publication. Its
private predicate was computed by the actual preceding comparison. -/
theorem protects_store {thread : Fin 256} (phase : Fin 9)
    (active : thread.val<Reduction.active phase) (ready : TreeControl thread s) :
    NativeFlow.Protects ctx (program count left right output scratch) (storeSite phase) s := by
  intro i t access index fetch actual early
  by_cases input : s.core.pc<20
  · rw [input_fetch input] at fetch
    obtain ⟨op,found,equal⟩ := Option.map_eq_some_iff.mp fetch
    cases equal
    have upper := NativeFlow.eval_upper actual input (input_syntax (List.mem_of_getElem? found)).1
    have lower : 22≤storeSite phase := by simp [storeSite]
    omega
  · have upper : s.core.pc<96 := by unfold storeSite at early; have := phase.isLt; omega
    have position : s.core.pc=20+(s.core.pc-20) := by omega
    rw [position,tree_fetch (by omega)] at fetch
    obtain ⟨native,found,equal⟩ := Option.map_eq_some_iff.mp fetch
    have checked := checked_store_protection phase ⟨s.core.pc-20,by omega⟩
    rw [found] at checked
    cases native <;> cases equal
    · cases actual with
      | data step => rw [Indexed.Candidate.data_pc step]; omega
      | simple ordinary => exact False.elim (ordinary _ rfl)
    · cases actual
      change s.core.pc+1≤storeSite phase
      omega
    · rename_i target
      cases actual
      change (if s.predicates 0=true then Flow.goto s (20+target) else Flow.next s).core.pc≤storeSite phase
      by_cases lands : 20+target≤storeSite phase
      · split <;> simp only [Flow.goto,Flow.next,advance] <;> omega
      · simp only [decide_eq_true_eq] at checked
        obtain ⟨bound,tag,large⟩ := checked (by omega) (by omega)
        have tag : treeGuard s.core.pc=some bound.val := by simpa only [← position] using tag
        have flag := ready.2 bound.val tag
        have untaken : s.predicates 0≠true := by
          intro taken
          have opposite := of_decide_eq_true (flag.symm.trans taken)
          omega
        simp only [ite_eq_right (by exact untaken),Flow.next,advance]
        omega

/-- Every later read has a real earlier publication from each lane active in
that publication phase, connected through the actual barrier round. -/
theorem publication_across {cfg : Config 256} {ctx : Fin 256 → Kernel.Context} {r : Nat}
    (run : NativeFlow.Runs cfg ctx (program count left right output scratch) start events indices final)
    (reset : start.core.barrier=Ptx.Barrier.reset generation)
    (entry : ∀ thread, (start.core.lanes thread).pc=0)
    (laneMap : ∀ thread, (ctx thread).lane.toNat=thread.val)
    (phase : Fin 9) (active : writer.val<Reduction.active phase)
    (observed : events[r]?=some (.data reader access)) (later : barrierSite phase<access.data.pc) :
    ∃ w wa, events[w]?=some (.data writer wa) ∧ wa.data.pc=storeSite phase ∧
      wa.data.store=true ∧ wa.space=.shared ∧ Visibility.Across events w r := by
  have aligned : Aligned start.core := by intro t h; simp [reset,Ptx.Barrier.reset] at h
  apply NativeFlow.producer_across (boundary:=barrierSite phase) run reset (store_fetch phase)
  · intro before earlier earlierIndices prior
    exact protects_store phase active (tree_control prior aligned entry laneMap writer)
  · rw [entry]; simp [storeSite]
  · simp [storeSite,barrierSite]
  · exact barrier_fetch phase
  · exact barrier_stops phase
  · intro t; rw [entry]; simp [barrierSite]
  · exact observed
  · exact later

end PtxTorchLean.Poisson.PTX.Concurrent.Dot

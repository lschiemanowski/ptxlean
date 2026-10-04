import PoissonPTX.DotPublicationSyntax
import PoissonPTX.NativeFlowBarrier

namespace PtxTorchLean.Poisson.PTX.Concurrent.Dot

def barrierSite (phase : Fin 9) : Nat := 23+9*phase.val

theorem checked_barriers : ∀ phase : Fin 9,
    Reduction.Native.code[3+9*phase.val]?=some (.sync 0) := by decide +kernel

theorem checked_barrier_targets : ∀ (phase : Fin 9) (slot : Fin 76),
    (match Reduction.Native.code[slot.val]? with
    | some (.branch target) => decide (slot.val≤3+9*phase.val → target≤3+9*phase.val)
    | _ => true)=true := by decide +kernel

theorem barrier_fetch (phase : Fin 9) :
    (program count left right output scratch)[barrierSite phase]?=some (.sync 0) := by
  have inside : 3+9*phase.val<76 := by have := phase.isLt; omega
  have position : barrierSite phase=20+(3+9*phase.val) := by simp [barrierSite]; omega
  rw [position,tree_fetch inside,checked_barriers]
  rfl

theorem barrier_stops (phase : Fin 9) :
    NativeFlow.StopsAt (program count left right output scratch) (barrierSite phase) := by
  intro pc i fetch before
  by_cases input : pc<20
  · rw [input_fetch input] at fetch
    obtain ⟨op,found,equal⟩ := Option.map_eq_some_iff.mp fetch
    cases equal
    have upper := (input_syntax (List.mem_of_getElem? found)).1
    cases i <;> simp_all [NativeFlow.targets,barrierSite] <;> omega
  · have phaseBound := phase.isLt
    have inside : pc<96 := by unfold barrierSite at before; omega
    have position : pc=20+(pc-20) := by omega
    rw [position,tree_fetch (by omega)] at fetch
    obtain ⟨native,found,equal⟩ := Option.map_eq_some_iff.mp fetch
    have checked := checked_barrier_targets phase ⟨pc-20,by omega⟩
    rw [found] at checked
    cases native <;> cases equal
    · trivial
    · trivial
    · simp only [decide_eq_true_eq] at checked
      have bounded := checked (by unfold barrierSite at before; omega)
      change 20+_≤barrierSite phase
      unfold barrierSite
      omega

/-- A lane beyond a native tree barrier entails an actual completed round and
prior arrivals from every lane in the same complete instruction history. -/
theorem passed_barrier
    (run : NativeFlow.Runs cfg ctx (program count left right output scratch) start events indices final)
    (reset : start.core.barrier=Ptx.Barrier.reset generation)
    (entry : (start.core.lanes owner).pc=0) (phase : Fin 9)
    (after : barrierSite phase<(final.core.lanes owner).pc) :
    ∃ (c : Nat) (key : Ptx.Barrier.Key), events[c]?=some (.barrier (.completion key)) ∧ key.site=barrierSite phase ∧
      ∀ thread, ∃ a : Nat, a<c ∧ events[a]?=some (.barrier (.arrival key thread)) := by
  have aligned : Aligned start.core := by intro thread waiting; simp [reset,Ptx.Barrier.reset] at waiting
  obtain ⟨key,completed,site⟩ := NativeFlow.crossed_barrier run aligned (barrier_fetch phase)
    (barrier_stops phase) (by simp [entry,barrierSite]) after
  obtain ⟨c,found⟩ := List.mem_iff_getElem?.mp completed
  exact ⟨c,key,found,site,NativeFlow.completed_arrivals run reset c key found⟩

end PtxTorchLean.Poisson.PTX.Concurrent.Dot

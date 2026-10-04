import PoissonPTX.DotBarriers
import PoissonPTX.NativeFlowHalting

namespace PtxTorchLean.Poisson.PTX.Concurrent.Dot

theorem continues_through_tree {pc : Nat} (before : pc≤96)
    (fetch : (program count left right output scratch)[pc]?=some (.flow i)) : NativeFlow.continues i := by
  by_cases input : pc<20
  · rw [input_fetch input] at fetch
    obtain ⟨op,found,equal⟩ := Option.map_eq_some_iff.mp fetch
    cases equal
    exact (input_syntax (List.mem_of_getElem? found)).2
  · by_cases tree : pc<96
    · have position : pc=20+(pc-20) := by omega
      rw [position,tree_fetch (by omega)] at fetch
      obtain ⟨native,_,equal⟩ := Option.map_eq_some_iff.mp fetch
      cases native <;> cases equal <;> trivial
    · have position : pc=96+0 := by omega
      rw [position,tail_fetch] at fetch
      change some (NativeFlow.Instr.flow (.compare 0 .ne (.reg 14) (.imm 0)))=some (.flow i) at fetch
      cases fetch
      trivial

theorem returned_after_tree
    (run : NativeFlow.Runs cfg ctx (program count left right output scratch) start events indices final)
    (live : ∀ thread, start.halted thread=false) (returned : final.halted owner=true) :
    96<(final.core.lanes owner).pc := by
  apply NativeFlow.runs_halted_after run (cut:=96) (fun thread halted => by simp [live] at halted)
    (fun pc i fetch before => continues_through_tree before fetch) owner returned

/-- Even a nonzero lane taking the conditional return has passed all nine
barriers; each completion has a real arrival from every participant. -/
theorem returned_barriers
    (run : NativeFlow.Runs cfg ctx (program count left right output scratch) start events indices final)
    (reset : start.core.barrier=Ptx.Barrier.reset generation)
    (entry : (start.core.lanes owner).pc=0) (live : ∀ thread, start.halted thread=false)
    (returned : final.halted owner=true) :
    ∀ phase : Fin 9, ∃ (c : Nat) (key : Ptx.Barrier.Key), events[c]?=some (.barrier (.completion key)) ∧ key.site=barrierSite phase ∧
      ∀ thread, ∃ a : Nat, a<c ∧ events[a]?=some (.barrier (.arrival key thread)) := by
  intro phase
  have done := returned_after_tree run live returned
  apply passed_barrier run reset entry phase
  have := phase.isLt
  unfold barrierSite
  omega

end PtxTorchLean.Poisson.PTX.Concurrent.Dot

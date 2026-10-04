import PoissonPTX.DotWitnessWords
import PoissonPTX.DotStoreProtection
import PoissonPTX.NativeFlowRound
import PoissonPTX.NativeFlowSerial
import PoissonPTX.ReductionWitnessLayout

namespace PtxTorchLean.Poisson.PTX.Concurrent.Dot.Witness
open Reduction.Control.Witness256

def ReadyAt (base pc generation : Nat) (s : NativeFlow.State 256) : Prop :=
  (∀ t, Frame base t (s.core.lanes t)) ∧ (∀ t, (s.core.lanes t).pc=pc) ∧
    (∀ t, s.halted t=false) ∧ s.core.barrier=Ptx.Barrier.reset generation ∧ s.core.site=none

theorem initial_fetch (j : Fin 3) :
    (program count left right output scratch)[20+j.val]?=
      ((SharedStore.code 0 8)[j.val]?).map (fun op => NativeFlow.Instr.flow (.data (.data op))) := by
  rw [tree_fetch (by have := j.isLt; omega)]
  fin_cases j <;> rfl

theorem update_fetch (phase : Fin 8) (j : Fin 6) :
    (program count left right output scratch)[26+9*phase.val+j.val]?=
      ((PTX.Reduction.Update.code (Reduction.Control.readOffset phase true))[j.val]?).map
        (fun op => NativeFlow.Instr.flow (.data (.data op))) := by
  have position : 26+9*phase.val+j.val=20+(6+9*phase.val+j.val) := by omega
  rw [position,tree_fetch (by have := phase.isLt; have := j.isLt; omega)]
  fin_cases phase <;> fin_cases j <;> rfl

theorem compare_fetch (phase : Fin 8) :
    (program count left right output scratch)[24+9*phase.val]?=
      some (.flow (.compare 0 .ge (.reg 14) (.imm (BitVec.ofNat 64 (stride phase))))) := by
  rw [show 24+9*phase.val=20+(4+9*phase.val) by omega,tree_fetch (by have := phase.isLt; omega)]
  fin_cases phase <;> rfl

theorem branch_fetch (phase : Fin 8) :
    (program count left right output scratch)[25+9*phase.val]?=
      some (.flow (.branch 0 true (barrierSite ⟨phase.val+1,by omega⟩))) := by
  rw [show 25+9*phase.val=20+(5+9*phase.val) by omega,tree_fetch (by have := phase.isLt; omega)]
  fin_cases phase <;> rfl

/-- The round contains every real arrival and completion, with no data events. -/
theorem round_expected (s : NativeFlow.State 256) (phase : Fin 9)
    (pcs : ∀ t, (s.core.lanes t).pc=barrierSite phase) (live : ∀ t, s.halted t=false)
    (reset : s.core.barrier=Ptx.Barrier.reset generation) (noSite : s.core.site=none) :
    ∃ events, NativeFlow.Runs cfg ctx (program count left right output scratch) s events [] (NativeFlow.afterRound s generation) ∧
      ∀ e∈events, Expected input e := by
  obtain ⟨events,run,barriers⟩ := NativeFlow.barrier_round_exists cfg s (program count left right output scratch)
    (barrierSite phase) generation pcs live reset noSite (barrier_fetch phase)
  refine ⟨events,run,?_⟩
  intro e member
  obtain ⟨b,rfl⟩ := barriers e member
  trivial

end PtxTorchLean.Poisson.PTX.Concurrent.Dot.Witness

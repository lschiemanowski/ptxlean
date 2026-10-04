import PoissonPTX.CellWitnessWave
import PoissonPTX.ReductionWitnessLayout

namespace PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.Witness
open CellMiddle Symbolic

theorem recorded_barriers (events : List (Event n)) (barriers : ∀ e∈events, ∃ b, e=.barrier b) :
    ByteHistory.Recorded memory events := by
  induction events with
  | nil => exact .nil
  | cons event rest ih =>
    obtain ⟨b,rfl⟩ := barriers event (by simp)
    exact .cons trivial (ih (fun e member => barriers e (by simp [member])))

theorem ready_round (ready : Ready width bases state) (pcs : ∀ t, (state.lanes t).pc=pc)
    (fetch : (program width)[pc]?=some (.sync 0)) : Ready width bases (afterRound state generation) := by
  constructor
  · intro t; exact ready.1 t
  · intro t active
    have value := ready.2 t active
    change Matches bases (fun _ _ => 0)
      (atPC .addresses (program width) (Numeric.seed width t.val) ((state.lanes t).pc+1)) (advance (state.lanes t))
    rw [pcs,at_next fetch]
    simpa only [pcs,transfer,Matches,advance] using value

/-- Complete the real full-block barrier after an arithmetic wave. Registers
and bytes are preserved; every lane advances only when all arrivals release it. -/
theorem round_exists (state : State n) (memory : Space → Memory)
    (ready : Ready width bases state) (pcs : ∀ t, (state.lanes t).pc=pc)
    (reset : state.barrier=Ptx.Barrier.reset generation) (site : state.site=none)
    (fetch : (program width)[pc]?=some (.sync 0))
    (forward : Forward (program width)) :
    ∃ events, Runs cfg (program width) state events (afterRound state generation) ∧
      ByteHistory.Recorded memory events ∧ Ready width bases (afterRound state generation) := by
  obtain ⟨events,run⟩ := barrier_round_exists cfg state (program width) pc generation pcs reset site fetch
  refine ⟨events,run,recorded_barriers events ?_,ready_round ready pcs fetch⟩
  intro e member
  exact Reduction.Control.Witness256.barrier_events run forward pcs (by intro t; simp [afterRound,advance,pcs]) fetch e member

end PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.Witness

import PoissonPTX.CellWitnessLaunch

namespace PtxTorchLean.Poisson.PTX.CellEntry

/-- Validate the future output stores using only launch indices, the allocated
output extent and metadata preserved by the real gather. -/
theorem witness_output {start final : State 32}
    (launch : Concurrent.CellMiddle.Numeric.Launch width bases (resume final))
    (result : ∀ u, lane final u=Local.finish (CellPrologue.threadContext bases cell u)
      width cells source (lane start u))
    (physical : ∀ u, Concurrent.CellConsumer.Witness.Allocation width bases (start.core.lanes u))
    (hi : width≤5) (aligned : output.toNat%8=0)
    (indices : ∀ u : Fin 32, cell.toNat*(width*width)+u.val<2^32)
    (fits : ∀ u : Fin 32, u.val<width*width → (cell.toNat*(width*width)+u.val)*8+output.toNat+8≤(start.core.lanes u).globalBytes) :
    ∀ u, u.val<width*width → Valid64 ((resume final).lanes u).globalStart ((resume final).lanes u).globalBytes
      (CellFinal.location ((resume final).lanes u) width output).toNat := by
  intro u active
  have ready := witness_ready launch result physical
  have arena := ready.1 u .global
  change ((resume final).lanes u).globalStart=(bases .global).toNat ∧
    ((resume final).lanes u).globalStart%8=0 ∧ _ at arena
  have cellReg : ((resume final).lanes u).regs 15=cell.setWidth 64 := by
    have same := congrArg (fun s : CellPrologue.State => s.core.regs 15) (result u)
    have kept := Local.finish_register (ctx:=CellPrologue.threadContext bases cell u)
      (width:=width) (cells:=cells) (source:=source) (s:=lane start u) (r:=15) (by decide)
    exact same.trans (kept.trans (by simp [CellPrologue.finish,CellPrologue.threadContext,Function.update]))
  have cellNat : (((resume final).lanes u).regs 15).toNat=cell.toNat := by
    rw [cellReg,BitVec.toNat_setWidth,Nat.mod_eq_of_lt (by have := cell.isLt; omega)]
  have sizes : ((resume final).lanes u).globalBytes=(start.core.lanes u).globalBytes := by
    have same := congrArg (fun s : CellPrologue.State => s.core.globalBytes) (result u)
    exact same.trans (Local.finish_allocation (ctx:=CellPrologue.threadContext bases cell u)
      (width:=width) (cells:=cells) (source:=source) (s:=lane start u) .global).2
  apply CellFinal.output_valid _ hi
  · simpa only [cellNat,launch.lane_nat] using indices u
  · rw [launch.global,arena.1]
  · exact arena.2.1
  · exact aligned
  · simpa only [cellNat,launch.lane_nat,sizes] using fits u active
  · exact arena.2.2.2

end PtxTorchLean.Poisson.PTX.CellEntry

import PoissonPTX.CellEntryIndexAddress
import PoissonPTX.CellTailBounds

namespace PtxTorchLean.Poisson.PTX.CellEntry.Control

/-- Input-array bounds relative to the output offset. They refer to launch IDs
and initial bytes, not the addresses or values of later executed reads. -/
structure InputLayout (memory : Memory) (ctx : CellPrologue.Context)
    (width : Nat) (cells source output : Word) where
  pointCount : Nat
  indexFits : ctx.cell.toNat*(width*width)+ctx.lane.toNat<2^32
  cellsEnd : cells.toNat+(ctx.cell.toNat*(width*width)+ctx.lane.toNat+1)*4≤output.toNat
  sourceEnd : source.toNat+pointCount*8≤output.toNat
  noWrap : ctx.arena.toNat+output.toNat≤2^64
  nodeBound : (read32 memory (ctx.arena.toNat+cells.toNat+
    (ctx.cell.toNat*(width*width)+ctx.lane.toNat)*4)).toNat<pointCount

theorem index_nat (bound : ctx.cell.toNat*(width*width)+ctx.lane.toNat<2^32) :
    (indexWord ctx width).toNat=ctx.cell.toNat*(width*width)+ctx.lane.toNat := by
  simpa [indexWord,BitVec.toNat_add,BitVec.toNat_mul,BitVec.toNat_ofNat,Nat.add_mod,Nat.mul_mod] using
    Nat.mod_eq_of_lt bound

theorem index_address (layout : InputLayout memory ctx width cells source output) :
    (ctx.arena+indexScale ctx width+cells).toNat=
      ctx.arena.toNat+cells.toNat+(ctx.cell.toNat*(width*width)+ctx.lane.toNat)*4 := by
  have idx := index_nat layout.indexFits
  have small : (ctx.cell.toNat*(width*width)+ctx.lane.toNat)*4<18446744073709551616 := by
    have := layout.indexFits; omega
  have endSmall : ctx.arena.toNat+(ctx.cell.toNat*(width*width)+ctx.lane.toNat)*4+cells.toNat<18446744073709551616 := by
    have := layout.cellsEnd; have := layout.noWrap; omega
  have midSmall : ctx.arena.toNat+(ctx.cell.toNat*(width*width)+ctx.lane.toNat)*4<2^64 := by omega
  simp only [BitVec.toNat_add,indexScale,BitVec.toNat_ofNat,idx,Nat.mod_eq_of_lt small,
    Nat.mod_eq_of_lt midSmall,Nat.mod_eq_of_lt endSmall]
  omega

theorem index_below (layout : InputLayout memory ctx width cells source output) :
    (ctx.arena+indexScale ctx width+cells).toNat+4≤ctx.arena.toNat+output.toNat := by
  rw [index_address layout]
  have := layout.cellsEnd; omega

/-- Every actual continuation output is at or beyond the output-array base.
This requires no admitted input reads. -/
theorem output_fence (lo : 2≤width) (hi : width≤5)
    (launch : Concurrent.CellMiddle.Numeric.Launch width bases start.core)
    (run : Concurrent.WithTail.Runs cfg bodyContext (Concurrent.CellConsumer.WithOutput.front width)
      (CellFinal.tail width output) start events final)
    (bounds : Concurrent.CellConsumer.WithOutput.OutputBounds width output start)
    (member : Concurrent.Event.data owner access∈events)
    (store : access.data.store=true) (global : access.space=.global) :
    (bases .global).toNat+output.toNat≤access.data.address := by
  rw [Concurrent.CellConsumer.WithOutput.Address.store_address lo hi run launch.aligned launch.pcs member store global]
  rw [CellFinal.location_exact _ hi (bounds owner).1 (bounds owner).2,launch.global]
  omega

end PtxTorchLean.Poisson.PTX.CellEntry.Control

import PoissonPTX.CellWholeCut

namespace PtxTorchLean.Poisson.PTX.CellWhole

/-- Nonwrapping output arithmetic from launch IDs, including padding lanes as
in the existing output-tail theorem. No executed address is a premise. -/
def OutputLayout (bases : Space → Word) (cell : BitVec 32) (width : Nat) (output : Word) : Prop :=
  ∀ u : Fin 32, cell.toNat*(width*width)+u.val<2^32 ∧
    (bases .global).toNat+(cell.toNat*(width*width)+u.val)*8+output.toNat<2^64

instance : Decidable (OutputLayout bases cell width output) := by
  unfold OutputLayout
  infer_instance

theorem output_bounds
    (first : CellEntry.Runs cfg (CellPrologue.threadContext bases cell) (CellEntry.program width cells source)
      (entry start) events indices (entry ready))
    (aligned : Concurrent.Aligned start.core) (pcs : ∀ u, (start.core.lanes u).pc=0)
    (done : ∀ u, (ready.core.lanes u).pc=21) (positive : 0<width) (fits : width*width<2^32)
    (layout : OutputLayout bases cell width output) :
    Concurrent.CellConsumer.WithOutput.OutputBounds width output (CellEntry.continuation (entry ready)) := by
  have control := CellEntry.Control.from_run first aligned
    (fun u => CellEntry.Control.initial (s:=CellEntry.lane (entry start) u) (pcs u)) positive fits
  intro u
  have past : 7≤(CellEntry.lane (entry ready) u).core.pc := by
    change 7≤(ready.core.lanes u).pc; rw [done]; decide
  have arena := (control u).2.1 (by omega)
  have lane := (control u).2.2.1 (by omega)
  have cellID := (control u).2.2.2.1 (by omega)
  have wide (v : BitVec 32) : (v.setWidth 64).toNat=v.toNat := by
    rw [BitVec.toNat_setWidth,Nat.mod_eq_of_lt]; have := v.isLt; omega
  change (ready.core.lanes u).regs 0=bases .global at arena
  change (ready.core.lanes u).regs 14=(BitVec.ofNat 32 u.val).setWidth 64 at lane
  change (ready.core.lanes u).regs 15=cell.setWidth 64 at cellID
  have small : u.val<4294967296 := by have := u.isLt; omega
  simpa only [CellEntry.continuation,CellEntry.resume,entry,arena,lane,cellID,wide,
    BitVec.toNat_ofNat,Nat.mod_eq_of_lt small] using layout u

end PtxTorchLean.Poisson.PTX.CellWhole

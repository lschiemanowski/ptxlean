import PoissonPTX.HostStorage
import PoissonPTX.CellWholeExists
import PoissonPTX.CellGridSchedule

namespace PtxTorchLean.Poisson.PTX.Host
open Concurrent

inductive CellEntryKind where
  | probe | direction | solution
  deriving DecidableEq, Repr

def CellEntryKind.entry : CellEntryKind → Entry
  | .probe => .elementProbe | .direction => .elementP | .solution => .elementX

def CellEntryKind.source : CellEntryKind → Field
  | .probe => .probe | .direction => .p | .solution => .x

/-- The cell instruction template addresses its three coefficient tables at
fixed offsets, including the real 32-byte buffer guards. -/
structure Layout.Coefficients (a : Layout n e w) : Prop where
  b : a.offset .b=0
  d : a.offset .d=BitVec.ofNat 64 (w*w*8+32)
  weight : a.offset .w=BitVec.ofNat 64 (2*(w*w*8+32))

def Layout.cellBases (a : Layout n e w) : Space → Word
  | .global => a.base
  | .shared => 0

def Layout.cellContext (a : Layout n e w) (block : Fin e) (thread : Fin 32) : Kernel.Context :=
  ⟨a.base,BitVec.ofNat 32 thread.val,BitVec.ofNat 32 block.val⟩

def Layout.cellStart (a : Layout n e w) (memory : Memory) (regs : Fin 32 → Registers) : CellEntry.State 32 :=
  ⟨⟨fun t => {(a.flowStart memory (regs t)).core with sharedBytes:=7*w*w*8},Ptx.Barrier.reset 0,none⟩,
    fun _ => false⟩

def Layout.cellLaunch (a : Layout n e w) (kind : CellEntryKind) : CellGrid.Launch e :=
  ⟨w,fun _ => a.cellBases,a.offset .cells,a.offset kind.source,a.offset .element,a.cellContext⟩

/-- Every connectivity word names an existing vector coordinate. These are
initial table bytes; no gathered value or execution outcome is supplied. -/
def Layout.Connectivity (a : Layout n e w) (memory : Memory) : Prop :=
  ∀ k<e*w*w, (read32 memory (a.slot .cells+k*4)).toNat<n

theorem Layout.cell_count (a : Layout n e w) : e < 2^32 := by
  have lo := a.lo
  have localSmall := a.localSmall
  have le : e≤e*w*w := (Nat.le_mul_of_pos_right e (by omega)).trans (Nat.le_mul_of_pos_right (e*w) (by omega))
  omega

theorem Layout.cell_index (a : Layout n e w) (block : Fin e) :
    (BitVec.ofNat 32 block.val).toNat=block.val := by
  exact Nat.mod_eq_of_lt (lt_trans block.isLt a.cell_count)

theorem Layout.cell_physical (a : Layout n e w) (tables : a.Coefficients)
    (memory : Memory) (regs : Fin 32 → Registers) (t : Fin 32) :
    CellConsumer.Witness.Allocation w a.cellBases ((a.cellStart memory regs).core.lanes t) := by
  have hi := a.hi
  have narrow : 2*(w*w*8+32)<2^64 := by nlinarith
  have coeff := a.fit .w
  rw [tables.weight] at coeff
  simp only [Field.count,Field.width,BitVec.toNat_ofNat,Nat.mod_eq_of_lt narrow] at coeff
  intro space
  cases space with
  | global => exact ⟨rfl,a.baseAligned,coeff,a.noWrap⟩
  | shared =>
    refine ⟨rfl,by change (0:Nat)%8=0; decide,le_rfl,?_⟩
    change 0+7*w*w*8≤2^64
    nlinarith

end PtxTorchLean.Poisson.PTX.Host

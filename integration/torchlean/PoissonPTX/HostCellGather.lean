import PoissonPTX.HostCellLayout

namespace PtxTorchLean.Poisson.PTX.Host

def Layout.beforeGather (a : Layout n e w) (memory : Memory) (regs : Fin 32 → Registers)
    (block : Fin e) (thread : Fin 32) : PTX.State :=
  CellEntry.Local.beforeGather (CellPrologue.threadContext a.cellBases (BitVec.ofNat 32 block.val) thread)
    w (CellEntry.lane (a.cellStart memory regs) thread)

/-- The actual entry instructions establish the pointer and launch-index
registers and preserve the allocation metadata and input bytes. -/
theorem Layout.gather_fields (a : Layout n e w) (memory : Memory) (regs : Fin 32 → Registers)
    (block : Fin e) (thread : Fin 32) :
    (a.beforeGather memory regs block thread).regs 0=a.base ∧
    (a.beforeGather memory regs block thread).regs 3=0 ∧
    ((a.beforeGather memory regs block thread).regs 14).toNat=thread.val ∧
    ((a.beforeGather memory regs block thread).regs 15).toNat=block.val ∧
    (a.beforeGather memory regs block thread).global=memory ∧
    (a.beforeGather memory regs block thread).globalStart=a.base.toNat ∧
    (a.beforeGather memory regs block thread).sharedStart=0 ∧
    (a.beforeGather memory regs block thread).globalBytes=a.bytes ∧
    (a.beforeGather memory regs block thread).sharedBytes=7*w*w*8 := by
  have smallThread : thread.val<2^32 := by have := thread.isLt; omega
  have smallBlock : block.val<2^32 := lt_trans block.isLt a.cell_count
  simp [Layout.beforeGather,CellEntry.Local.beforeGather,CellPrologue.finish,CellPrologue.threadContext,
    CellEntry.lane,Layout.cellStart,Layout.cellBases,Layout.flowStart,advance,
    BitVec.toNat_setWidth,BitVec.toNat_ofNat]
  constructor <;> omega

def Layout.gatherLayout (a : Layout n e w) (kind : CellEntryKind) (memory : Memory)
    (connected : a.Connectivity memory) (regs : Fin 32 → Registers) (block : Fin e) (thread : Fin 32)
    (active : thread.val<w*w) :
    CellGather.Layout (a.beforeGather memory regs block thread) w (a.offset .cells) (a.offset kind.source) := by
  obtain ⟨base,scratch,lane,cell,mem,start,shared,bytes,sharedBytes⟩ := a.gather_fields memory regs block thread
  refine {
    cellCount:=e,pointCount:=n,
    globalBase:=by rw [base,start],
    sharedBase:=by rw [scratch,shared]; rfl,
    globalAligned:=by rw [start]; exact a.baseAligned,
    sharedAligned:=by rw [shared],
    cellsAligned:=a.align_width .cells,
    sourceAligned:=a.aligned _,
    cell:=by rw [cell]; exact block.isLt,
    active:=by rw [lane]; exact active,
    widthBound:=a.hi,
    indexFits:=by simpa only [Nat.mul_assoc] using lt_trans a.localSmall (by decide : 2^30<2^32),
    cellsFit:=?_,sourceFit:=?_,sharedFit:=by rw [sharedBytes],
    globalNoWrap:=by rw [start,bytes]; exact a.noWrap,
    sharedNoWrap:=?_,connectivity:=?_ }
  · rw [bytes]
    simpa [Field.count,Field.width,Nat.mul_assoc] using a.fit .cells
  · rw [bytes]; cases kind <;> exact a.fit _
  · rw [shared,sharedBytes]; have := a.hi; nlinarith
  · intro k bound
    rw [mem,start]
    apply connected k
    simpa only [Nat.mul_assoc] using bound

/-- Physical allocation covers every actual cell output word. Extra lanes
need no vector allocation because their guard returns before the store. -/
theorem Layout.cell_output (a : Layout n e w) (block : Fin e) (thread : Fin 32)
    (active : thread.val<w*w) :
    (BitVec.ofNat 32 block.val).toNat*(w*w)+thread.val<2^32 ∧
    ((BitVec.ofNat 32 block.val).toNat*(w*w)+thread.val)*8+(a.offset .element).toNat+8≤a.bytes := by
  rw [a.cell_index block]
  have extent := a.fit .element
  change (a.offset .element).toNat+e*w*w*8≤a.bytes at extent
  have product := Nat.mul_le_mul_right (w*w) (show block.val+1≤e from block.isLt)
  simp only [Nat.add_mul,Nat.one_mul] at product
  have small := a.localSmall
  rw [Nat.mul_assoc e w w] at extent small
  constructor <;> omega

end PtxTorchLean.Poisson.PTX.Host

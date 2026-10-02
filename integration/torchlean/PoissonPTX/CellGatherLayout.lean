import PoissonPTX.CellGather

namespace PtxTorchLean.Poisson.PTX.CellGather

/-- Nonwrapping cell/lane index into the four-byte connectivity array. -/
theorem index_exact (bound : (s.regs 15).toNat*(width*width)+(s.regs 14).toNat<2^32) :
    (index s width).toNat=(s.regs 15).toNat*(width*width)+(s.regs 14).toNat := by
  simpa [index,Kernel.u32,BitVec.toNat_add,BitVec.toNat_mul,BitVec.toNat_ofNat,
    BitVec.toNat_setWidth,Nat.add_mod,Nat.mul_mod] using Nat.mod_eq_of_lt bound

/-- Contiguous-array conditions on input storage. Connectivity values must be
valid source-vector indices; no floating output value is assumed. -/
structure Layout (s : State) (width : Nat) (cells source : Word) where
  cellCount : Nat
  pointCount : Nat
  globalBase : (s.regs 0).toNat=s.globalStart
  sharedBase : (s.regs 3).toNat=s.sharedStart
  globalAligned : s.globalStart%8=0
  sharedAligned : s.sharedStart%8=0
  cellsAligned : cells.toNat%4=0
  sourceAligned : source.toNat%8=0
  cell : (s.regs 15).toNat<cellCount
  active : (s.regs 14).toNat<width*width
  widthBound : width≤5
  indexFits : cellCount*(width*width)<2^32
  cellsFit : cells.toNat+cellCount*(width*width)*4≤s.globalBytes
  sourceFit : source.toNat+pointCount*8≤s.globalBytes
  sharedFit : 7*width*width*8≤s.sharedBytes
  globalNoWrap : s.globalStart+s.globalBytes≤2^64
  sharedNoWrap : s.sharedStart+s.sharedBytes≤2^64
  connectivity : ∀ k<cellCount*(width*width),
    (read32 s.global (s.globalStart+cells.toNat+k*4)).toNat<pointCount

theorem index_inside (layout : Layout s width cells source) :
    (s.regs 15).toNat*(width*width)+(s.regs 14).toNat<layout.cellCount*(width*width) := by
  have a := Nat.mul_le_mul_right (width*width) (show (s.regs 15).toNat+1≤layout.cellCount by have := layout.cell; omega)
  have := layout.active
  nlinarith

theorem connectivity_address (layout : Layout s width cells source) :
    (connectivityAddress s width cells).toNat=s.globalStart+cells.toNat+
      ((s.regs 15).toNat*(width*width)+(s.regs 14).toNat)*4 := by
  have inside := index_inside layout
  have idx := index_exact (lt_trans inside layout.indexFits)
  have bound : (s.regs 0).toNat+(index s width).toNat*4+cells.toNat<2^64 := by
    rw [layout.globalBase,idx]
    have := layout.cellsFit; have := layout.globalNoWrap; omega
  rw [connectivityAddress,address32_exact _ _ _ bound,layout.globalBase,idx]
  omega

theorem node_inside (layout : Layout s width cells source) :
    (node s width cells).toNat<layout.pointCount := by
  unfold node
  rw [connectivity_address layout]
  exact layout.connectivity _ (index_inside layout)

theorem valid_of_layout (layout : Layout s width cells source) : Valid s width cells source := by
  have inside := index_inside layout
  have idx := index_exact (lt_trans inside layout.indexFits)
  refine ⟨?_,?_,?_⟩
  · have alignment : s.globalStart%4=0 := by have := layout.globalAligned; omega
    have valid := valid32_of_array (s.regs 0) cells (layout.cellCount*(width*width))
      s.globalBytes (index s width) (by rw [layout.globalBase]; exact alignment)
      layout.cellsAligned (by rw [idx]; exact inside) layout.cellsFit
      (by rw [layout.globalBase]; exact layout.globalNoWrap)
    simpa [connectivityAddress,layout.globalBase] using valid
  · have nodeBound := node_inside layout
    have bound : (s.regs 0).toNat+(node s width cells).toNat*8+source.toNat<2^64 := by
      rw [layout.globalBase]; have := layout.sourceFit; have := layout.globalNoWrap; omega
    rw [sourceAddress,address64_exact _ _ _ bound,layout.globalBase]
    refine ⟨by omega,?_,?_,layout.globalNoWrap⟩
    · simp [Nat.add_mod,layout.globalAligned,layout.sourceAligned]
    · have := layout.sourceFit; omega
  · have live := layout.active
    have small : width*width≤25 := by have := layout.widthBound; nlinarith
    have narrow : (Kernel.u32 (s.regs 14)).toNat=(s.regs 14).toNat := by
      simp only [Kernel.u32,BitVec.toNat_setWidth,Nat.mod_eq_of_lt (show (s.regs 14).toNat<2^32 by omega)]
    have wideSmall : (s.regs 14).toNat*8<2^64 := by omega
    have endSmall : s.sharedStart+(s.regs 14).toNat*8<2^64 := by
      have := layout.sharedFit; have := layout.sharedNoWrap; nlinarith
    simp only [destination,BitVec.toNat_add,BitVec.toNat_ofNat,narrow,
      Nat.mod_eq_of_lt wideSmall,layout.sharedBase,Nat.mod_eq_of_lt endSmall]
    refine ⟨by omega,?_,?_,layout.sharedNoWrap⟩
    · simp [Nat.add_mod,layout.sharedAligned]
    · have := layout.sharedFit; nlinarith

end PtxTorchLean.Poisson.PTX.CellGather

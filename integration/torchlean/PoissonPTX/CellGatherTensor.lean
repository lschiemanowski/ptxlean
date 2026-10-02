import PoissonPTX.CellGatherLayout
import PoissonQuad

namespace PtxTorchLean.Poisson.PTX.CellGather

/-- The source index is derived from actual bytes. Input representation relates
those bytes to the TorchLean connectivity table and vector, not to an output. -/
theorem torchlean (o : Operator) (values : Array Float) (e : Nat)
    (layout : Layout s o.nodes.size cells source)
    (cell : (s.regs 15).toNat=e) (i j : Fin o.nodes.size)
    (lane : (s.regs 14).toNat=i.val*o.nodes.size+j.val)
    (connectivity : ∀ k<o.nodes.size*o.nodes.size,
      (read32 s.global (s.globalStart+cells.toNat+(e*(o.nodes.size*o.nodes.size)+k)*4)).toNat=
        (o.mesh.cells[e]!)[k]!)
    (contents : ∀ k<layout.pointCount,
      decode (read64 s.global (s.globalStart+source.toNat+k*8))=values[k]!)
    (run : Indexed.Block (code o.nodes.size cells source) s t) :
    decode (read64 t.shared (destination s).toNat)=Spec.get2 (gather o values e) i j := by
  have idx := node_inside layout
  have address := connectivity_address layout
  rw [cell,lane] at address
  have coord : i.val*o.nodes.size+j.val<o.nodes.size*o.nodes.size := by
    have := i.isLt; have := j.isLt; nlinarith
  have nodeEq : (node s o.nodes.size cells).toNat=(o.mesh.cells[e]!)[i.val*o.nodes.size+j.val]! := by
    unfold node
    rw [address]
    exact connectivity _ coord
  have bound : (s.regs 0).toNat+(node s o.nodes.size cells).toNat*8+source.toNat<2^64 := by
    rw [layout.globalBase]; have := layout.sourceFit; have := layout.globalNoWrap; omega
  rw [(stored run (valid_of_layout layout)).1]
  unfold value sourceAddress
  rw [address64_exact _ _ _ bound,layout.globalBase]
  have permute : s.globalStart+(node s o.nodes.size cells).toNat*8+source.toNat=
      s.globalStart+source.toNat+(node s o.nodes.size cells).toNat*8 := by omega
  rw [permute,contents _ idx,nodeEq]
  simp [gather,matrix,Spec.get2,Spec.get,TorchLean.Tensor.getScalar,
    TorchLean.Tensor.unstack,TorchLean.Tensor.item]

end PtxTorchLean.Poisson.PTX.CellGather

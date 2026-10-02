import PoissonPTX.CellEntryPublication

namespace PtxTorchLean.Poisson.PTX.CellEntry

/-- The copied launch IDs identify the cell and matrix position without an
additional coordinate invariant supplied by the caller. -/
theorem before_ids (bases : Space → Word) (cell : BitVec 32) (owner : Fin 32)
    (s : CellPrologue.State) :
    ((Local.beforeGather (CellPrologue.threadContext bases cell owner) width s).regs 15).toNat=cell.toNat ∧
    ((Local.beforeGather (CellPrologue.threadContext bases cell owner) width s).regs 14).toNat=owner.val := by
  have small : owner.val<4294967296 := by have := owner.isLt; omega
  simp [Local.beforeGather,CellPrologue.threadContext,CellPrologue.finish,advance,BitVec.toNat_setWidth,
    BitVec.toNat_ofNat,Nat.mod_eq_of_lt small]
  have := cell.isLt; have := owner.isLt
  constructor <;> omega

/-- All entries of the source-rebased input matrix are TorchLean's connectivity
gather. The premises describe input arrays and allocated memory, never an
already-computed tensor or a desired floating-point result. -/
theorem publication_torchlean (o : Operator) (values : Array Float)
    (run : Runs cfg (CellPrologue.threadContext bases cell) (program o.nodes.size cells source) s events indices t)
    (aligned : Concurrent.Aligned s.core) (initial : ∀ u, (s.core.lanes u).global=memory .global)
    (words : Concurrent.Visibility.Compatible memory events chosen)
    (indexSources : IndexSources.Compatible (memory .global) events indices selected)
    (pcs : ∀ u, (s.core.lanes u).pc=0) (done : ∀ u, (t.core.lanes u).pc=21)
    (positive : 0<o.nodes.size) (small : o.nodes.size*o.nodes.size≤32)
    (space : (bases .shared).toNat+7*o.nodes.size*o.nodes.size*8≤2^64)
    (layout : ∀ u : Fin 32, u.val<o.nodes.size*o.nodes.size →
      CellGather.Layout (Local.beforeGather (CellPrologue.threadContext bases cell u) o.nodes.size (lane s u))
        o.nodes.size cells source)
    (connectivity : ∀ u : Fin 32, u.val<o.nodes.size*o.nodes.size → ∀ k<o.nodes.size*o.nodes.size,
      (read32 (s.core.lanes u).global ((s.core.lanes u).globalStart+cells.toNat+
        (cell.toNat*(o.nodes.size*o.nodes.size)+k)*4)).toNat=(o.mesh.cells[cell.toNat]!)[k]!)
    (contents : ∀ (u : Fin 32) (active : u.val<o.nodes.size*o.nodes.size), ∀ k<(layout u active).pointCount,
      decode (read64 (s.core.lanes u).global ((s.core.lanes u).globalStart+source.toNat+k*8))=values[k]!) :
    Concurrent.CellMiddle.Numeric.initialTensor o.nodes.size bases
      (publication o.nodes.size small bases memory t) .shared 0=Poisson.gather o values cell.toNat := by
  apply TorchLean.Tensor.Internal.Rep.ext
  intro coordinate
  rcases coordinate with ⟨i,j,remaining⟩
  cases remaining
  have active : i.val*o.nodes.size+j.val<o.nodes.size*o.nodes.size := by
    have := i.isLt; have := j.isLt; nlinarith
  let owner : Fin 32 := ⟨i.val*o.nodes.size+j.val,by omega⟩
  have laneActive : (CellPrologue.threadContext bases cell owner).lane.toNat<o.nodes.size*o.nodes.size := by
    rw [context_lane]; exact active
  have ids := before_ids (width:=o.nodes.size) bases cell owner (lane s owner)
  have result := gathered_torchlean o values cell.toNat run aligned initial words indexSources owner
    (pcs owner) (done owner) positive (by omega) laneActive (layout owner active) ids.1 i j ids.2
    (connectivity owner active) (contents owner active)
  rw [destination_address bases cell owner (lane s owner) active space] at result
  rw [← publication_lane (bases:=bases) (memory:=memory) (t:=t) small owner active] at result
  have nowrap : (bases .shared).toNat+(i.val*o.nodes.size+j.val)*8<18446744073709551616 := by nlinarith
  simpa [Nat.mod_eq_of_lt nowrap,Concurrent.CellMiddle.Numeric.initialTensor,Concurrent.CellMiddle.Numeric.grid,matrix,
    Spec.get2,Spec.get,TorchLean.Tensor.getScalar,TorchLean.Tensor.unstack,TorchLean.Tensor.item,owner] using result

end PtxTorchLean.Poisson.PTX.CellEntry

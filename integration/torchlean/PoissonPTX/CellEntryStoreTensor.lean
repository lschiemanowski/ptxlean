import PoissonPTX.CellEntryStoreValue

namespace PtxTorchLean.Poisson.PTX.CellEntry
variable {n : Nat} {s t : State n} {cfg : Concurrent.Config n}
  {ctx : Fin n → CellPrologue.Context}

/-- The value in an actual store record, rather than only the lane's local
memory, agrees with TorchLean's cell-input gather. -/
theorem recorded_torchlean (o : Operator) (values : Array Float) (e : Nat)
    (run : Runs cfg ctx (program o.nodes.size cells source) s events indices t)
    (aligned : Concurrent.Aligned s.core) (initial : ∀ u, (s.core.lanes u).global=memory .global)
    (words : Concurrent.Visibility.Compatible memory events chosen)
    (indexSources : IndexSources.Compatible (memory .global) events indices selected)
    (thread : Fin n) (pc : (s.core.lanes thread).pc=0) (done : (t.core.lanes thread).pc=21)
    (positive : 0<o.nodes.size) (fits : o.nodes.size*o.nodes.size<2^32)
    (active : (ctx thread).lane.toNat<o.nodes.size*o.nodes.size)
    (layout : CellGather.Layout (Local.beforeGather (ctx thread) o.nodes.size (lane s thread)) o.nodes.size cells source)
    (cell : ((Local.beforeGather (ctx thread) o.nodes.size (lane s thread)).regs 15).toNat=e)
    (i j : Fin o.nodes.size)
    (coordinate : ((Local.beforeGather (ctx thread) o.nodes.size (lane s thread)).regs 14).toNat=i.val*o.nodes.size+j.val)
    (connectivity : ∀ k<o.nodes.size*o.nodes.size,
      (read32 (s.core.lanes thread).global ((s.core.lanes thread).globalStart+cells.toNat+(e*(o.nodes.size*o.nodes.size)+k)*4)).toNat=
        (o.mesh.cells[e]!)[k]!)
    (contents : ∀ k<layout.pointCount,
      decode (read64 (s.core.lanes thread).global ((s.core.lanes thread).globalStart+source.toNat+k*8))=values[k]!)
    (member : Concurrent.Event.data thread access∈events) (store : access.data.store=true) :
    decode access.data.value=Spec.get2 (Poisson.gather o values e) i j := by
  have recorded := recorded_gather run aligned initial words indexSources pc done positive fits active
    (CellGather.valid_of_layout layout) member store
  have copied := recorded_store run member store
  rw [← copied.2.2.2.2,recorded.1]
  exact gathered_torchlean o values e run aligned initial words indexSources thread pc done positive fits
    active layout cell i j coordinate connectivity contents

end PtxTorchLean.Poisson.PTX.CellEntry

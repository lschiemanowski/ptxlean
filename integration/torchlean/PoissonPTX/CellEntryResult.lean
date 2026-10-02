import PoissonPTX.CellEntryReplay

namespace PtxTorchLean.Poisson.PTX.CellEntry

theorem Local.finish_pc (pc : s.core.pc=0) :
    (Local.finish ctx width cells source s).core.pc=21 := by
  simp only [Local.finish]
  split <;> simp [advance,CellGather.finish,Local.beforeGather,CellPrologue.finish,pc]

variable {n : Nat} {s t : State n} {cfg : Concurrent.Config n}
  {ctx : Fin n → CellPrologue.Context}

/-- All instructions through the first barrier are accounted for. The final
lane state is derived from a concurrent run and input-byte compatibility. -/
theorem completed_lane (run : Runs cfg ctx (program width cells source) s events indices t)
    (aligned : Concurrent.Aligned s.core) (initial : ∀ u, (s.core.lanes u).global=memory .global)
    (words : Concurrent.Visibility.Compatible memory events chosen)
    (indexSources : IndexSources.Compatible (memory .global) events indices selected)
    (thread : Fin n) (pc : (s.core.lanes thread).pc=0) (done : (t.core.lanes thread).pc=21)
    (positive : 0<width) (fits : width*width<2^32)
    (valid : (ctx thread).lane.toNat<width*width →
      CellGather.Valid (Local.beforeGather (ctx thread) width (lane s thread)) width cells source) :
    lane t thread=Local.finish (ctx thread) width cells source (lane s thread) := by
  apply Local.terminal_unique (actual_trace run aligned initial words indexSources thread)
    (Local.exists_trace _ _ pc positive fits valid)
  · simp only [lane,done,List.getElem?_eq_none_iff,program_length]; omega
  · simp only [Local.finish_pc (s:=lane s thread) pc,List.getElem?_eq_none_iff,program_length]; omega

/-- Even a NaN payload is copied exactly. This is the lane's actual shared
store result, not yet the separate cross-thread visibility conclusion. -/
theorem gathered_bits (run : Runs cfg ctx (program width cells source) s events indices t)
    (aligned : Concurrent.Aligned s.core) (initial : ∀ u, (s.core.lanes u).global=memory .global)
    (words : Concurrent.Visibility.Compatible memory events chosen)
    (indexSources : IndexSources.Compatible (memory .global) events indices selected)
    (thread : Fin n) (pc : (s.core.lanes thread).pc=0) (done : (t.core.lanes thread).pc=21)
    (positive : 0<width) (fits : width*width<2^32)
    (active : (ctx thread).lane.toNat<width*width)
    (valid : CellGather.Valid (Local.beforeGather (ctx thread) width (lane s thread)) width cells source) :
    read64 (t.core.lanes thread).shared
      (CellGather.destination (Local.beforeGather (ctx thread) width (lane s thread))).toNat=
    CellGather.value (Local.beforeGather (ctx thread) width (lane s thread)) width cells source := by
  have result := completed_lane run aligned initial words indexSources thread pc done positive fits (fun _ => valid)
  have live : (CellPrologue.finish (ctx thread) width (lane s thread)).live=true := by
    simp [CellPrologue.finish,active]
  have mem := congrArg (fun q => q.core.shared) result
  change (t.core.lanes thread).shared=_ at mem
  rw [mem]
  simp only [Local.finish,live,↓reduceIte,advance,CellGather.finish]
  exact read64_write64 _ _ _

/-- Input representation is the only tensor premise. The index and copied
word have already been recovered from the executed concurrent instructions. -/
theorem gathered_torchlean (o : Operator) (values : Array Float) (e : Nat)
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
      decode (read64 (s.core.lanes thread).global ((s.core.lanes thread).globalStart+source.toNat+k*8))=values[k]!) :
    decode (read64 (t.core.lanes thread).shared
      (CellGather.destination (Local.beforeGather (ctx thread) o.nodes.size (lane s thread))).toNat)=
        Spec.get2 (Poisson.gather o values e) i j := by
  have valid := CellGather.valid_of_layout layout
  have bits := gathered_bits run aligned initial words indexSources thread pc done positive fits active valid
  rw [bits]
  have localRun := Indexed.run_sound (CellGather.execution valid)
  have tensor := CellGather.torchlean o values e layout cell i j coordinate connectivity contents localRun
  simpa only [CellGather.finish,read64_write64] using tensor

end PtxTorchLean.Poisson.PTX.CellEntry

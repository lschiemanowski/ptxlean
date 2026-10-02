import PoissonPTX.CellEntryPadding

namespace PtxTorchLean.Poisson.PTX.CellEntry

theorem context_lane (bases : Space → Word) (cell : BitVec 32) (thread : Fin 32) :
    (CellPrologue.threadContext bases cell thread).lane.toNat=thread.val := by
  simp only [CellPrologue.threadContext,BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt (by have := thread.isLt; omega)

theorem destination_context (bases : Space → Word) (cell : BitVec 32) (thread : Fin 32)
    (s : CellPrologue.State) :
    CellGather.destination (Local.beforeGather (CellPrologue.threadContext bases cell thread) width s)=
      bases .shared+BitVec.ofNat 64 (thread.val*8) := by
  have small : thread.val<4294967296 := by have := thread.isLt; omega
  simp [CellGather.destination,Local.beforeGather,CellPrologue.finish,CellPrologue.threadContext,
    Kernel.u32,advance,BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt small]

theorem destination_address (bases : Space → Word) (cell : BitVec 32) (thread : Fin 32)
    (s : CellPrologue.State) (active : thread.val<width*width)
    (space : (bases .shared).toNat+7*width*width*8≤2^64) :
    (CellGather.destination (Local.beforeGather (CellPrologue.threadContext bases cell thread) width s)).toNat=
      (bases .shared).toNat+thread.val*8 := by
  rw [destination_context]
  have small : thread.val*8<2^64 := by have := thread.isLt; omega
  have bound : (bases .shared).toNat+thread.val*8<2^64 := by nlinarith
  simp only [BitVec.toNat_add,BitVec.toNat_ofNat,Nat.mod_eq_of_lt small,Nat.mod_eq_of_lt bound]

variable {n : Nat} {s t : State n} {cfg : Concurrent.Config n}
  {ctx : Fin n → CellPrologue.Context}

/-- Addresses and stored bits are consequences of the same completed run. -/
theorem recorded_gather (run : Runs cfg ctx (program width cells source) s events indices t)
    (aligned : Concurrent.Aligned s.core) (initial : ∀ u, (s.core.lanes u).global=memory .global)
    (words : Concurrent.Visibility.Compatible memory events chosen)
    (indexSources : IndexSources.Compatible (memory .global) events indices selected)
    (pc : (s.core.lanes owner).pc=0) (done : (t.core.lanes owner).pc=21)
    (positive : 0<width) (fits : width*width<2^32) (active : (ctx owner).lane.toNat<width*width)
    (valid : CellGather.Valid (Local.beforeGather (ctx owner) width (lane s owner)) width cells source)
    (member : Concurrent.Event.data owner access∈events) (store : access.data.store=true) :
    access.data.address=(CellGather.destination (Local.beforeGather (ctx owner) width (lane s owner))).toNat ∧
    access.data.value=CellGather.value (Local.beforeGather (ctx owner) width (lane s owner)) width cells source := by
  have final := completed_lane run aligned initial words indexSources owner pc done positive fits (fun _ => valid)
  have live : (CellPrologue.finish (ctx owner) width (lane s owner)).live=true := by
    simp [CellPrologue.finish,active]
  have address := congrArg (fun q => q.core.regs 2) final
  have value := congrArg (fun q => q.core.regs 11) final
  simp [Local.finish,live,CellGather.finish,advance] at address value
  have actual := recorded_store run member store
  exact ⟨actual.2.2.1.trans (congrArg BitVec.toNat address),actual.2.2.2.1.trans value⟩

end PtxTorchLean.Poisson.PTX.CellEntry

import PoissonPTX.CellEntryResult
import PoissonPTX.CellEntryBarrier

namespace PtxTorchLean.Poisson.PTX.CellEntry

theorem Local.finish_register (untouched : r≠1 ∧ r≠2 ∧ r≠11 ∧ r≠13 ∧ r≠18) :
    (Local.finish ctx width cells source s).core.regs r=(CellPrologue.finish ctx width s).core.regs r := by
  simp only [Local.finish]
  split <;> simp [advance,CellGather.finish,Function.update,untouched,Local.beforeGather]

/-- Changing the instruction-number origin retains all memories, registers,
allocation metadata and the actual barrier state. It performs no GPU step. -/
def resume (s : State 32) : Concurrent.State 32 :=
  {s.core with lanes:=fun t => {s.core.lanes t with pc:=(s.core.lanes t).pc-21}}

/-- The arithmetic launch contract is now derived from the real entry prefix.
Shared input visibility and the continuation's byte-source restriction are
separate obligations; no shared memory is installed by this theorem. -/
theorem arithmetic_launch
    (run : Runs cfg (CellPrologue.threadContext bases cell) (program width cells source) s events indices t)
    (aligned : Concurrent.Aligned s.core) (initial : ∀ u, (s.core.lanes u).global=memory .global)
    (words : Concurrent.Visibility.Compatible memory events chosen)
    (indexSources : IndexSources.Compatible (memory .global) events indices selected)
    (pcs : ∀ u, (s.core.lanes u).pc=0)
    (thread : Fin 32) (finished : 20<(t.core.lanes thread).pc)
    (positive : 0<width) (fits : width*width<2^32)
    (space : (bases .shared).toNat+7*width*width*8≤2^64)
    (valid : ∀ u, (CellPrologue.threadContext bases cell u).lane.toNat<width*width →
      CellGather.Valid (Local.beforeGather (CellPrologue.threadContext bases cell u) width (lane s u)) width cells source) :
    Nonempty (Concurrent.CellMiddle.Numeric.Launch width bases (resume t)) := by
  obtain ⟨done,site,generation,key,barrier,_,_⟩ := completed_barrier run aligned
    (fun u => by rw [pcs]; omega) thread finished
  have result (u : Fin 32) := completed_lane run aligned initial words indexSources u (pcs u) (done u)
    positive fits (valid u)
  have registers (u : Fin 32) := CellPrologue.thread_registers
    (CellPrologue.fetched_exists (CellPrologue.threadContext bases cell u) (lane s u) (pcs u) positive fits)
    (pcs u) positive fits
  have retained (u : Fin 32) (r : Nat) (keep : r≠1 ∧ r≠2 ∧ r≠11 ∧ r≠13 ∧ r≠18) :
      (t.core.lanes u).regs r=(CellPrologue.finish (CellPrologue.threadContext bases cell u) width (lane s u)).core.regs r := by
    have h := congrArg (fun q => q.core.regs r) (result u)
    exact h.trans (Local.finish_register keep)
  refine ⟨⟨generation+1,barrier,?_,?_,?_,?_,?_,?_,space⟩⟩
  · intro u; simp [resume,done]
  · intro u; exact (retained u 0 (by decide)).trans (registers u).1
  · intro u; exact (retained u 3 (by decide)).trans (registers u).2.1
  · intro u; exact (retained u 14 (by decide)).trans (registers u).2.2.1
  · intro u; exact (retained u 16 (by decide)).trans (registers u).2.2.2.2.1
  · intro u; exact (retained u 17 (by decide)).trans (registers u).2.2.2.2.2.1

end PtxTorchLean.Poisson.PTX.CellEntry

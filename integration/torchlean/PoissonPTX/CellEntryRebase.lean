import PoissonPTX.CellEntryPublication
import PoissonPTX.CellOutputTensor

namespace PtxTorchLean.Poisson.PTX.CellEntry
open Ptx

variable {cfg : Concurrent.Config 32} {bases : Space → Word} {cell : BitVec 32}
  {width : Nat} {cells source : Word} {s t : State 32}
  {events : List (Concurrent.Event 32)} {indices : List (Fin 32 × IndexSources.Access)}
  {memory : Space → Memory} {chosen : Nat → Fin 8 → Sources.Origin Nat}
  {selected : Nat → Fin 4 → Sources.Origin Nat}

/- These are the entry theorem's execution, input representation and safety
premises, shared by the producer lemmas below. None asserts a store or answer. -/
variable (run : Runs cfg (CellPrologue.threadContext bases cell) (program width cells source) s events indices t)
  (aligned : Concurrent.Aligned s.core) (initial : ∀ u, (s.core.lanes u).global=memory .global)
  (words : Concurrent.Visibility.Compatible memory events chosen)
  (indexSources : IndexSources.Compatible (memory .global) events indices selected)
  (pcs : ∀ u, (s.core.lanes u).pc=0) (done : ∀ u, (t.core.lanes u).pc=21)
  (positive : 0<width) (fits : width*width<2^32)
  (space : (bases .shared).toNat+7*width*width*8≤2^64)
  (valid : ∀ u : Fin 32, u.val<width*width →
    CellGather.Valid (Local.beforeGather (CellPrologue.threadContext bases cell u) width (lane s u)) width cells source)

include run aligned initial words indexSources pcs done positive fits space valid

/-- Restrict the one whole-history source assignment to the actual body,
using the prefix's proved publication as its initial-byte view. No state is
replaced and no read values are assumed. Prefix input admission remains explicit. -/
theorem body_sources {later : List (Concurrent.Event 32)}
    (lo : 2≤width) (hi : width≤5) (small : width*width≤32)
    (body : Concurrent.WithTail.Runs cfg bodyContext (Concurrent.CellConsumer.WithOutput.front width)
      (CellFinal.tail width output) (continuation t) later final)
    (reset : s.core.barrier=Barrier.reset generation)
    (joint : Concurrent.Visibility.Compatible memory (events++later) allSources)
    (performed : Concurrent.Visibility.Performed (events++later) allSources) :
    Concurrent.Visibility.Compatible (publication width small bases memory t) later
      (Concurrent.SourceCut.source events.length allSources) ∧
    Concurrent.Visibility.Performed later (Concurrent.SourceCut.source events.length allSources) := by
  obtain ⟨launch⟩ := arithmetic_launch run aligned initial words indexSources pcs (0 : Fin 32)
    (by rw [done]; omega) positive fits space (fun u h => valid u (by simpa only [context_lane] using h))
  constructor
  · exact Concurrent.SourceCut.compatible
      (publication_sound run aligned initial words indexSources pcs done positive fits space valid small)
      (publication_ordered run aligned pcs done reset)
      joint performed
  · apply Concurrent.SourceCut.performed ?_ joint performed
    intro writer wa member store other wb member' store' same j k overlap
    have info := Producers.info run aligned initial words indexSources pcs done positive fits space valid member store
    have shared : wb.space=.shared := same.symm.trans info.2.1
    have disjoint := Concurrent.CellConsumer.WithOutput.preserves_gather launch lo hi body
      member' store' shared writer info.1
    rw [info.2.2.1] at overlap
    rw [Sources.Disjoint] at disjoint
    have := j.isLt; have := k.isLt
    omega

/-- Numerical body correspondence now follows from the real gather, real first
barrier and one joint source history, with a proved publication as input view.
The snapshot is not installed in the execution. -/
theorem body_result {later : List (Concurrent.Event 32)}
    (lo : 2≤width) (hi : width≤5) (small : width*width≤32)
    (body : Concurrent.WithTail.Runs cfg bodyContext (Concurrent.CellConsumer.WithOutput.front width)
      (CellFinal.tail width output) (continuation t) later final)
    (reset : s.core.barrier=Barrier.reset generation)
    (bounds : Concurrent.CellConsumer.WithOutput.OutputBounds width output (continuation t))
    (offset : Concurrent.CellConsumer.Coefficients.extent width≤output.toNat)
    (joint : Concurrent.Visibility.Compatible memory (events++later) allSources)
    (performed : Concurrent.Visibility.Performed (events++later) allSources)
    (thread : Fin 32) (i j : Fin width) (coordinate : thread.val=i.val*width+j.val)
    (finished : (Concurrent.CellConsumer.program width).length≤(final.core.lanes thread).pc) :
    decode ((final.core.lanes thread).regs 11)=Spec.get2 (localAction
      (Concurrent.CellMiddle.Numeric.initialTensor width bases memory .global 0)
      (Concurrent.CellMiddle.Numeric.initialTensor width bases memory .global (width*width*8+32))
      (Concurrent.CellMiddle.Numeric.initialTensor width bases memory .global (2*(width*width*8+32)))
      (Concurrent.CellMiddle.Numeric.initialTensor width bases (publication width small bases memory t) .shared 0)) i j := by
  obtain ⟨launch⟩ := arithmetic_launch run aligned initial words indexSources pcs thread
    (by rw [done]; omega) positive fits space (fun u h => valid u (by simpa only [context_lane] using h))
  have sources := body_sources run aligned initial words indexSources pcs done positive fits space valid
    lo hi small body reset joint performed
  exact Concurrent.CellConsumer.WithOutput.result_from_launch launch lo hi body bounds offset
    sources.1 sources.2 thread i j coordinate finished

/-- The cell ID in the actual continuation is copied from launch context. -/
theorem continued_cell (owner : Fin 32) :
    ((continuation t).core.lanes owner).regs 15=cell.setWidth 64 := by
  have result := completed_lane run aligned initial words indexSources owner (pcs owner) (done owner)
    positive fits (fun h => valid owner (by simpa only [context_lane] using h))
  have registers := congrArg (fun q => q.core.regs 15) result
  have preserved := Local.finish_register (s:=lane s owner)
    (ctx:=CellPrologue.threadContext bases cell owner) (width:=width) (cells:=cells) (source:=source)
    (r:=15) (by decide)
  exact registers.trans (preserved.trans (by simp [CellPrologue.finish,CellPrologue.threadContext]))

/-- Actual output records, in any publication order, form the numerical cell
result using the input view derived from the real gathered stores. -/
theorem published_result {later order : List (Concurrent.Event 32)}
    (lo : 2≤width) (hi : width≤5) (small : width*width≤32)
    (body : Concurrent.WithTail.Runs cfg bodyContext (Concurrent.CellConsumer.WithOutput.front width)
      (CellFinal.tail width output) (continuation t) later final)
    (reset : s.core.barrier=Barrier.reset generation)
    (bounds : Concurrent.CellConsumer.WithOutput.OutputBounds width output (continuation t))
    (offset : Concurrent.CellConsumer.Coefficients.extent width≤output.toNat)
    (joint : Concurrent.Visibility.Compatible memory (events++later) allSources)
    (performed : Concurrent.Visibility.Performed (events++later) allSources)
    (permutation : order.Perm later)
    (finished : ∀ u : Fin 32, u.val<width*width →
      (Concurrent.CellConsumer.WithOutput.front width).length+5≤(final.core.lanes u).pc) :
    Concurrent.CellConsumer.WithOutput.Publication.tensor width (bases .global) (cell.setWidth 64) output
      (Concurrent.GlobalPublication.publish outputMemory order)=localAction
        (Concurrent.CellMiddle.Numeric.initialTensor width bases memory .global 0)
        (Concurrent.CellMiddle.Numeric.initialTensor width bases memory .global (width*width*8+32))
        (Concurrent.CellMiddle.Numeric.initialTensor width bases memory .global (2*(width*width*8+32)))
        (Concurrent.CellMiddle.Numeric.initialTensor width bases (publication width small bases memory t) .shared 0) := by
  obtain ⟨launch⟩ := arithmetic_launch run aligned initial words indexSources pcs (0 : Fin 32)
    (by rw [done]; omega) positive fits space (fun u h => valid u (by simpa only [context_lane] using h))
  have sources := body_sources run aligned initial words indexSources pcs done positive fits space valid
    lo hi small body reset joint performed
  have result := Concurrent.CellConsumer.WithOutput.Publication.published_tensor
    (width:=width) (bases:=bases) (cell:=cell.setWidth 64) (start:=continuation t) (final:=final)
    (events:=later) (order:=order) (memory:=outputMemory)
    (initial:=publication width small bases memory t)
    (original:=Concurrent.SourceCut.source events.length allSources)
    launch lo hi body bounds offset
    (continued_cell run aligned initial words indexSources pcs done positive fits space valid)
    sources.1 sources.2 permutation finished
  have globalViews (off : Nat) : Concurrent.CellMiddle.Numeric.initialTensor width bases
      (publication width small bases memory t) .global off=
      Concurrent.CellMiddle.Numeric.initialTensor width bases memory .global off := rfl
  rw [globalViews,globalViews,globalViews] at result
  exact result

end PtxTorchLean.Poisson.PTX.CellEntry

import PoissonPTX.CellWitnessOutput
import PoissonPTX.CellWholeCompose
import PoissonPTX.ByteHistoryRelocate

namespace PtxTorchLean.Poisson.PTX.CellWhole
open Concurrent.CellConsumer

/-- Arbitrary valid inputs admit a complete fetched cell execution. Its four
barrier rounds, output stores and padding returns are constructed. Read bytes
come from the initial memory or actual preceding stores in this same run. -/
theorem exists_recorded (cfg : Concurrent.Config 32) (ctx : Fin 32 → Kernel.Context)
    (start : CellEntry.State 32) (memory : Space → Memory)
    (lo : 2≤width) (hi : width≤5)
    (pcs : ∀ u, (start.core.lanes u).pc=0)
    (reset : start.core.barrier=Ptx.Barrier.reset generation) (site : start.core.site=none)
    (initial : ∀ u, (start.core.lanes u).global=memory .global)
    (physical : ∀ u, Witness.Allocation width bases (start.core.lanes u))
    (valid : ∀ u, (CellPrologue.threadContext bases cell u).lane.toNat<width*width →
      CellGather.Valid (CellEntry.Local.beforeGather (CellPrologue.threadContext bases cell u)
        width (CellEntry.lane start u)) width cells source)
    (aligned : output.toNat%8=0)
    (indices : ∀ u : Fin 32, cell.toNat*(width*width)+u.val<2^32)
    (fits : ∀ u : Fin 32, u.val<width*width → (cell.toNat*(width*width)+u.val)*8+output.toNat+8≤(start.core.lanes u).globalBytes) :
    ∃ final events indexEvents,
      Runs cfg bases cell width cells source output ctx (begin start) events indexEvents final ∧
      Concurrent.ByteHistory.Recorded memory events ∧
      CellEntry.Indices (memory .global) indexEvents ∧
      (∀ u, final.halted u=true) ∧
      (∀ u, (final.core.lanes u).pc=21+(WithOutput.front width).length+6) ∧
      final.core.barrier=Ptx.Barrier.reset (generation+4) ∧ final.core.site=none := by
  have positive : 0<width := by omega
  have small : width*width<2^32 := by nlinarith
  have initialAligned : Concurrent.Aligned start.core := by
    intro u waiting; simp [reset,Ptx.Barrier.reset] at waiting
  obtain ⟨ready,before,indexEvents,first,done,barrier,empty,words,indexWords⟩ :=
    CellEntry.prefix_exists cfg (CellPrologue.threadContext bases cell) start pcs reset site initial positive small valid
  have firstRecords := CellEntry.recorded_prefix first words (memory:=memory)
  obtain ⟨compatible,_,indexCompatible⟩ := CellEntry.initial_sources first words indexWords (memory:=memory)
  have result (u) := CellEntry.completed_lane first initialAligned initial compatible indexCompatible u
    (pcs u) (done u) positive small (valid u)
  have sharedSpace : (bases .shared).toNat+7*width*width*8≤2^64 := by
    have allocation := physical (0 : Fin 32) .shared
    change (start.core.lanes 0).sharedStart=(bases .shared).toNat ∧ _ at allocation
    have extent := allocation.2.2.1
    change 7*width*width*8≤(start.core.lanes 0).sharedBytes at extent
    have nowrap := allocation.2.2.2
    change (start.core.lanes 0).sharedStart+(start.core.lanes 0).sharedBytes≤2^64 at nowrap
    omega
  obtain ⟨launch⟩ := CellEntry.Control.launch first initialAligned pcs done positive small sharedSpace
  have inputReady := CellEntry.witness_ready launch result physical
  have outputValid := CellEntry.witness_output launch result physical hi aligned indices fits
  obtain ⟨final,after,body,bodyRecords,halted,finished,finalBarrier,finalSite⟩ :=
    Witness.body_exists (cfg:=cfg) (ctx:=ctx) (CellEntry.continuation ready)
      (Concurrent.ByteHistory.publish memory before) lo hi inputReady launch.pcs (fun _ => rfl)
      barrier empty outputValid
  refine ⟨Relocate.tailState 21 final,before++after.map (Relocate.event 21),indexEvents,
    compose first done empty body,
    Concurrent.ByteHistory.recorded_append firstRecords (Concurrent.ByteHistory.recorded_relocate bodyRecords),
    indexWords,halted,?_,?_,?_⟩
  · intro u
    change (final.core.lanes u).pc+21=21+(WithOutput.front width).length+6
    rw [finished]; omega
  · change final.core.barrier=Ptx.Barrier.reset (generation+4)
    simpa only [Nat.add_assoc] using finalBarrier
  · change final.core.site.map (·+21)=none
    rw [finalSite]; rfl

/-- Necessary source admission for the constructed whole history, including
four-byte connectivity reads. This is not full PTX memory-model admission. -/
theorem recorded_sources (recorded : Concurrent.ByteHistory.Recorded memory events)
    (indices : CellEntry.Indices (memory .global) indexEvents) :
    Concurrent.Visibility.Compatible memory events (Concurrent.ByteHistory.sources events) ∧
      Concurrent.Visibility.Performed events (Concurrent.ByteHistory.sources events) ∧
      IndexSources.Compatible (memory .global) events indexEvents (fun _ _ => .initial) := by
  obtain ⟨compatible,performed⟩ := Concurrent.ByteHistory.recorded_admitted recorded
  refine ⟨compatible,performed,?_⟩
  intro r reader a found k
  change IndexSources.byte32 a.value k.val=memory .global (a.address+k.val)
  rw [indices reader a (List.mem_of_getElem? found)]
  exact IndexSources.byte_read32 _ _ k

end PtxTorchLean.Poisson.PTX.CellWhole

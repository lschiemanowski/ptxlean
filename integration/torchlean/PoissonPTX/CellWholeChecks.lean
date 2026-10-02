import PoissonPTX.CellWholeCompose
import PoissonPTX.CellWholeSources
import PoissonPTX.CellEntryRebaseChecks

namespace PtxTorchLean.Poisson.PTX.CellWhole.Checks
open CellEntry CellEntry.Checks CellEntry.RebaseChecks
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

def events := result.events++bodyResult.events.map (Relocate.event 21)
def final := Relocate.tailState 21 bodyResult.state

attribute [local irreducible] result bodyResult events final

/-- The nonzero gather and cross-lane read are one native-counter execution. -/
theorem actual : Runs cfg bases 1 2 0 64 256 bodyContext (begin start)
    events result.indices final := by
  unfold events final
  exact compose actual_run completed.1 completed.2.2.1 actual_body

/-- Real data records keep the emitted kernel's absolute instruction counters. -/
theorem shifted_reads : bodyResult.events.map (Relocate.event 21)=[
    .data 2 ⟨.global,⟨28,false,4112,0x100000003⟩⟩,
    .data 2 ⟨.shared,⟨33,false,256,0xc000000000000000⟩⟩] := by
  rw [reads]; rfl

theorem native_pc : (final.core.lanes 2).pc=34 := by decide +kernel

theorem checked : Concurrent.SourceCheck.Checked initial events RebaseChecks.sources := by decide +kernel

theorem admitted : Concurrent.Visibility.Compatible initial events RebaseChecks.sources :=
  Concurrent.SourceCheck.sound (initial:=initial) (events:=events) (source:=RebaseChecks.sources) checked

/-- Cutting the single execution recovers a genuine fetched continuation;
neither its boundary nor its instruction/event counter translation is assumed. -/
theorem extracted : ∃ prefixEvents bodyEvents ready localFinal,
    events=prefixEvents++bodyEvents.map (Relocate.event 21) ∧
    CellEntry.Runs cfg ctx kernel start prefixEvents result.indices ready ∧
    (∀ u, (ready.core.lanes u).pc=21) ∧ ready.core.site=none ∧
    final=Relocate.tailState 21 localFinal ∧
    Concurrent.WithTail.Runs cfg bodyContext (Concurrent.CellConsumer.WithOutput.front 2)
      (CellFinal.tail 2 256) (CellEntry.continuation ready) bodyEvents localFinal := by
  obtain ⟨a,b,r,t,h⟩ := executions actual ProducerChecks.aligned (by intro u; rfl) (by intro u; rfl) 2
    (by rw [native_pc]; decide)
  exact ⟨a,b,entry r,t,h⟩

/-- Barrier identity includes both generation and the absolute instruction site. -/
theorem barrier_sites :
    Concurrent.Relabel.renameAfter 1 21 ⟨0,0,0,20⟩=⟨0,0,0,20⟩ ∧
    Concurrent.Relabel.renameAfter 1 21 ⟨0,0,1,20⟩=⟨0,0,1,41⟩ := by decide +kernel

end PtxTorchLean.Poisson.PTX.CellWhole.Checks

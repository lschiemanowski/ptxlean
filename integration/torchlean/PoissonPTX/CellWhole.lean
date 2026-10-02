import PoissonPTX.OffsetExecution
import PoissonPTX.CellEntryJointCorrespondence

namespace PtxTorchLean.Poisson.PTX.CellWhole

abbrev State := Concurrent.WithTail.State 32

def entry (s : State) : CellEntry.State 32 := ⟨s.core,s.predicate⟩

def entryState (s : State) (next : CellEntry.State 32) : State :=
  ⟨next.core,next.live,s.halted⟩

structure Outcome where
  state : State
  events : List (Concurrent.Event 32)
  indices : List (Fin 32 × IndexSources.Access)

/-- One fetched execution of the entry, arithmetic and output tail. Prefix
fetching ends at 21; the body uses absolute counters and relocated branch and
barrier sites. There is no externally supplied cut or transition schedule. -/
inductive Step (cfg : Concurrent.Config 32) (bases : Space → Word) (cell : BitVec 32)
    (width : Nat) (cells source output : Word) (ctx : Fin 32 → Kernel.Context) :
    Fin 32 → State → Outcome → Prop where
  | entry (running : s.halted thread=false)
      (step : CellEntry.Step cfg (CellPrologue.threadContext bases cell) (CellEntry.program width cells source)
        thread (entry s) out) :
      Step cfg bases cell width cells source output ctx thread s
        ⟨entryState s out.state,out.events,out.indices⟩
  | body (step : Concurrent.AtOffset.Step 21 cfg ctx (Concurrent.CellConsumer.WithOutput.front width)
      (CellFinal.tail width output) thread s out) :
      Step cfg bases cell width cells source output ctx thread s ⟨out.state,out.events,[]⟩

inductive Runs (cfg : Concurrent.Config 32) (bases : Space → Word) (cell : BitVec 32)
    (width : Nat) (cells source output : Word) (ctx : Fin 32 → Kernel.Context) :
    State → List (Concurrent.Event 32) → List (Fin 32 × IndexSources.Access) → State → Prop where
  | nil : Runs cfg bases cell width cells source output ctx s [] [] s
  | cons : Step cfg bases cell width cells source output ctx thread s out →
      Runs cfg bases cell width cells source output ctx out.state events indices final →
      Runs cfg bases cell width cells source output ctx s (out.events++events) (out.indices++indices) final

theorem step_aligned (step : Step cfg bases cell width cells source output ctx thread s out)
    (aligned : Concurrent.Aligned s.core) : Concurrent.Aligned out.state.core := by
  cases step with
  | entry _ one => exact CellEntry.step_aligned one aligned
  | body one => exact Concurrent.AtOffset.aligned one aligned

/-- Before the first barrier, a full-entry step must be a real prefix step. -/
theorem before (step : Step cfg bases cell width cells source output ctx thread s out)
    (early : (s.core.lanes thread).pc≤20) :
    CellEntry.Step cfg (CellPrologue.threadContext bases cell) (CellEntry.program width cells source)
      thread (entry s) ⟨entry out.state,out.events,out.indices⟩ ∧ out.state.halted=s.halted := by
  cases step with
  | entry _ one => exact ⟨one,rfl⟩
  | body one => cases one <;> omega

/-- The first real release determines the cut and preserves every register,
byte and flag. All thirty-two lanes, including padding, have reached it. -/
theorem split (run : Runs cfg bases cell width cells source output ctx start events indices final)
    (aligned : Concurrent.Aligned start.core)
    (early : ∀ u, (start.core.lanes u).pc≤20) (running : ∀ u, start.halted u=false)
    (thread : Fin 32) (finished : 20<(final.core.lanes thread).pc) :
    ∃ first later firstIndices laterIndices ready,
      events=first++later ∧ indices=firstIndices++laterIndices ∧
      CellEntry.Runs cfg (CellPrologue.threadContext bases cell) (CellEntry.program width cells source)
        (entry start) first firstIndices (entry ready) ∧
      (∀ u, (ready.core.lanes u).pc=21) ∧ ready.core.site=none ∧
      (∀ u, ready.halted u=false) ∧
      Runs cfg bases cell width cells source output ctx ready later laterIndices final := by
  induction run with
  | nil => have := early thread; omega
  | @cons selected s out rest indexRest final one tail ih =>
    have prefixStep := before one (early selected)
    have nextRunning : ∀ u, out.state.halted u=false := by rw [prefixStep.2]; exact running
    by_cases crossed : ∃ u, 20<(out.state.core.lanes u).pc
    · obtain ⟨u,hu⟩ := crossed
      obtain ⟨pcs,site,remaining⟩ := CellEntry.crossing prefixStep.1 aligned u (early u) hu
      exact ⟨out.events,rest,out.indices,indexRest,out.state,rfl,rfl,
        by simpa using CellEntry.Runs.cons prefixStep.1 CellEntry.Runs.nil,pcs,site,nextRunning,tail⟩
    · obtain ⟨first,later,firstIndices,laterIndices,ready,eventEq,indexEq,firstRun,pcs,site,readyRunning,last⟩ :=
        ih (step_aligned one aligned) (fun u => by have := not_exists.mp crossed u; omega) nextRunning finished
      exact ⟨out.events++first,later,out.indices++firstIndices,laterIndices,ready,
        by simp [eventEq,List.append_assoc],by simp [indexEq,List.append_assoc],
        .cons prefixStep.1 firstRun,pcs,site,readyRunning,last⟩

end PtxTorchLean.Poisson.PTX.CellWhole

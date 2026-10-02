import PoissonPTX.CellWholeCut

namespace PtxTorchLean.Poisson.PTX.CellWhole

variable {before after : List (Concurrent.Event 32)}

def begin (s : CellEntry.State 32) : State := ⟨s.core,s.live,fun _ => false⟩

theorem append (first : Runs cfg bases cell width cells source output ctx s before firstIndices t)
    (second : Runs cfg bases cell width cells source output ctx t after lastIndices u) :
    Runs cfg bases cell width cells source output ctx s (before++after) (firstIndices++lastIndices) u := by
  induction first with
  | nil => exact second
  | cons one rest ih => simpa [List.append_assoc] using Runs.cons one (ih second)

theorem prefix_run
    (run : CellEntry.Runs cfg (CellPrologue.threadContext bases cell) (CellEntry.program width cells source)
      s events indices t) :
    Runs cfg bases cell width cells source output ctx (begin s) events indices (begin t) := by
  induction run with
  | nil => exact .nil
  | cons one rest ih => exact .cons (.entry rfl one) ih

theorem offset_run
    (run : Concurrent.AtOffset.Runs 21 cfg ctx (Concurrent.CellConsumer.WithOutput.front width)
      (CellFinal.tail width output) s events t) :
    Runs cfg bases cell width cells source output ctx s events [] t := by
  induction run with
  | nil => exact .nil
  | cons one rest ih => exact .cons (.body one) ih

/-- Construct a full fetched run by composing actual steps. The first barrier
must really have completed; no shared snapshot is installed at the join. -/
theorem compose
    (first : CellEntry.Runs cfg (CellPrologue.threadContext bases cell) (CellEntry.program width cells source)
      s before indices ready)
    (pcs : ∀ u, (ready.core.lanes u).pc=21) (site : ready.core.site=none)
    (body : Concurrent.WithTail.Runs cfg ctx (Concurrent.CellConsumer.WithOutput.front width)
      (CellFinal.tail width output) (CellEntry.continuation ready) after final) :
    Runs cfg bases cell width cells source output ctx (begin s)
      (before++after.map (Relocate.event 21)) indices (Relocate.tailState 21 final) := by
  have shifted : begin ready=Relocate.tailState 21 (CellEntry.continuation ready) :=
    ready_view (ready:=begin ready) pcs site (fun _ => rfl)
  have later := offset_run (bases:=bases) (cell:=cell) (cells:=cells) (source:=source)
    (Concurrent.AtOffset.run_forward (origin:=21) body)
  rw [← shifted] at later
  simpa using append (prefix_run first) later

end PtxTorchLean.Poisson.PTX.CellWhole

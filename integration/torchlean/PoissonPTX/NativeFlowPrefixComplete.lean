import PoissonPTX.NativeFlowPrefix

namespace PtxTorchLean.Poisson.PTX.Concurrent.NativeFlow

/-- A syntax check: neither unconditional nor conditional return appears. -/
def continues : Flow.Instr → Prop
  | .ret | .predRet .. => False
  | _ => True

theorem eval_live (actual : Flow.Observed.Eval ctx i s t access index)
    (ordinary : continues i) (live : s.halted=false) : t.halted=false := by
  cases actual with
  | data => exact live
  | simple =>
    cases i <;> simp_all [continues,Flow.simple,Flow.next,Flow.goto]
    all_goals split <;> simp_all

theorem observed_live (run : Flow.Observed.Runs ctx pre s words indices t)
    (ordinary : ∀ i∈pre, continues i) (live : s.halted=false) : t.halted=false := by
  induction run with
  | nil => exact live
  | cons step rest ih =>
    obtain ⟨_,i,fetch,actual⟩ := step
    exact ih (eval_live actual (ordinary i (List.mem_of_getElem? fetch)) live)

/-- A returned thread has really completed its nonreturning prefix. Its
projected execution reaches the boundary, with observed loads retained. -/
theorem prefix_complete (region : Region program pre)
    (ordinary : ∀ i∈pre, continues i)
    (actual : Runs cfg ctx program s events indices t) (aligned : Aligned s.core)
    (start : (s.core.lanes owner).pc≤pre.length) (live : s.halted owner=false)
    (returned : t.halted owner=true) :
    ∃ next words localIndices,
      Flow.Observed.Runs (ctx owner) pre (lane s owner) words localIndices next ∧
      next.core.pc=pre.length ∧ next.halted=false ∧
      (∀ a∈words, Event.data owner a∈events) ∧ (∀ a∈localIndices, (owner,a)∈indices) := by
  obtain ⟨next,words,indices,run,related,wordMem,indexMem⟩ :=
    prefix_run region actual aligned (related_initial (lane s owner) start)
  have stillLive := observed_live run ordinary live
  refine ⟨next,words,indices,run,?_,stillLive,wordMem,indexMem⟩
  unfold Related at related
  split at related
  · have same := congrArg Flow.State.halted related
    simp only [lane] at same
    rw [returned,stillLive] at same
    cases same
  · exact related

end PtxTorchLean.Poisson.PTX.Concurrent.NativeFlow

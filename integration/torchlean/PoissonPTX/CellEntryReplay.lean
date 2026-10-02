import PoissonPTX.CellEntryLocal

namespace PtxTorchLean.Poisson.PTX.CellEntry

def Words (initial : Memory) (events : List (Concurrent.Event n)) : Prop :=
  ∀ thread a, Concurrent.Event.data thread a∈events → a.data.store=false → a.space=.global →
    a.data.value=read64 initial a.data.address

def Indices (initial : Memory) (indices : List (Fin n × IndexSources.Access)) : Prop :=
  ∀ thread a, (thread,a)∈indices → a.value=read32 initial a.address

variable {n : Nat} {s t : State n} {out : Outcome n} {cfg : Concurrent.Config n}
  {ctx : Fin n → CellPrologue.Context}

/-- Project one genuine concurrent step to a chosen lane. A collective release
advances that lane only at the same fetched barrier as all other participants. -/
theorem step_local (step : Step cfg ctx (program width cells source) selected s out)
    (aligned : Concurrent.Aligned s.core) (initial : ∀ t, (s.core.lanes t).global=memory)
    (words : Words memory out.events) (indices : Indices memory out.indices) (thread : Fin n) :
    lane s thread=lane out.state thread ∨
      Local.Step (ctx thread) (program width cells source) (lane s thread) (lane out.state thread) := by
  obtain ⟨fresh,i,fetch,dispatch⟩ := step
  cases dispatch with
  | setup he =>
    by_cases same : thread=selected
    · subst thread
      right; refine ⟨_,fetch,?_⟩
      simpa [Local.eval,lane,setLane,Concurrent.setLane] using he
    · left; simp [lane,setLane,Concurrent.setLane,Function.update,same]
  | gather he =>
    by_cases same : thread=selected
    · subst thread
      have replay := Indexed.Candidate.replay he (fun a observed read => ?_) (fun a observed => ?_)
      · right; refine ⟨_,fetch,?_⟩
        have canonical := Indexed.eval_complete replay (gather_plain fetch)
        simp [Local.eval,lane,Concurrent.setLane,canonical]
      · have global := Indexed.Candidate.load_global (observed ▸ he) (gather_safe fetch).2 read
        rw [global]
        change a.data.value=read64 (s.core.lanes selected).global a.data.address
        rw [initial selected]
        exact words selected a (by simp [observed]) read global
      · rw [initial selected]
        exact indices selected a (by simp [observed])
    · left; simp [lane,Concurrent.setLane,Function.update,same]
  | skip =>
    by_cases same : thread=selected
    · subst thread
      right; refine ⟨_,fetch,?_⟩
      simp [Local.eval,lane,Concurrent.setLane]
      rfl
    · left; simp [lane,Concurrent.setLane,Function.update,same]
  | sync =>
    let c := Concurrent.barrierConfig cfg s.core selected
    let r := Concurrent.barrierRequest cfg s.core selected 0
    generalize hr : Ptx.Barrier.step c s.core.barrier r=result
    cases disposition : result.disposition with
    | rejectedWrongKey =>
      left; simp [lane,synchronize,Concurrent.synchronize,← show c=Concurrent.barrierConfig cfg s.core selected from rfl,
        ← show r=Concurrent.barrierRequest cfg s.core selected 0 from rfl,hr,disposition]
    | waiting =>
      left; simp [lane,synchronize,Concurrent.synchronize,← show c=Concurrent.barrierConfig cfg s.core selected from rfl,
        ← show r=Concurrent.barrierRequest cfg s.core selected 0 from rfl,hr,disposition]
    | released =>
      have pcs := Concurrent.release_aligned cfg s.core selected 0 aligned (by change (Ptx.Barrier.step c s.core.barrier r).disposition=_; rw [hr,disposition])
      right; refine ⟨.sync,?_,?_⟩
      · change (program width cells source)[(s.core.lanes thread).pc]?=_
        rw [pcs thread]; exact fetch
      · simp [Local.eval,lane,synchronize,Concurrent.synchronize,← show c=Concurrent.barrierConfig cfg s.core selected from rfl,
          ← show r=Concurrent.barrierRequest cfg s.core selected 0 from rfl,hr,disposition]

theorem runs_local (run : Runs cfg ctx (program width cells source) s events indices t)
    (aligned : Concurrent.Aligned s.core) (initial : ∀ t, (s.core.lanes t).global=memory)
    (words : Words memory events) (indexValues : Indices memory indices) (thread : Fin n) :
    Local.Runs (ctx thread) (program width cells source) (lane s thread) (lane t thread) := by
  induction run with
  | nil => exact .nil
  | @cons selected s out events indices final step rest ih =>
    have projected :=  step_local step aligned initial
      (fun t a member read global => words t a (List.mem_append_left _ member) read global)
      (fun t a member => indexValues t a (List.mem_append_left _ member)) thread
    have tail := ih (step_aligned step aligned) (fun t => (step_global step t).trans (initial t))
      (fun t a member read global => words t a (List.mem_append_right _ member) read global)
      (fun t a member => indexValues t a (List.mem_append_right _ member))
    rcases projected with equal | one
    · rw [equal]; exact tail
    · exact .cons one tail

/-- A local execution is derived from one concurrent history and its necessary
byte-source constraints. Neither input read values nor local traces are premises. -/
theorem actual_trace (run : Runs cfg ctx (program width cells source) s events indices t)
    (aligned : Concurrent.Aligned s.core) (initial : ∀ t, (s.core.lanes t).global=memory .global)
    (words : Concurrent.Visibility.Compatible memory events chosen)
    (indexSources : IndexSources.Compatible (memory .global) events indices selected)
    (thread : Fin n) :
    Local.Runs (ctx thread) (program width cells source) (lane s thread) (lane t thread) := by
  apply runs_local run aligned initial
  · intro thread a member read global
    obtain ⟨r,observed⟩ := List.mem_iff_getElem?.mp member
    exact word_value run words observed read global
  · intro thread a member
    obtain ⟨r,observed⟩ := List.mem_iff_getElem?.mp member
    exact index_value run indexSources observed

end PtxTorchLean.Poisson.PTX.CellEntry

import PtxBinary32.Parallel

/-! Finite witnesses for fetched full-group barrier rounds and resource reuse.
These are control executions; no shared-memory visibility is assumed or claimed. -/
namespace Ptx.Scalar.Parallel

/-- The abstract release changes only the program counters and barrier fields. -/
def afterRound (s : State n) (generation : Nat) : State n :=
  { lanes := fun t =>
      { scalar := {(s.lanes t).scalar with pc := (s.lanes t).scalar.pc + 1}
        halted := (s.lanes t).halted }
    global := s.global
    shared := s.shared
    barrier := Barrier.reset (generation+1)
    site := none }


/-- A concrete increasing-thread schedule, before its final arrival. -/
def roundPrefix (s : State n) (pc generation count : Nat) : State n :=
  if count = n then afterRound s generation else
    {s with barrier := Barrier.prefixState generation count,site := if count=0 then none else some pc}

private theorem prefix_dispatch (cfg : Config n) (s : State n) (program : List Instr)
    (pc generation count : Nat) (bound : count < n)
    (pcs : ∀ t, (s.lanes t).scalar.pc = pc) (live : ∀ t, (s.lanes t).halted = false)
    (fetch : program[pc]? = some (.sync 0)) (eligible : Mixed.Eligible cfg.target) :
    ∃ out, Step cfg program none ⟨count,bound⟩ (roundPrefix s pc generation count) out ∧
      out.state = roundPrefix s pc generation (count+1) := by
  let t : Fin n := ⟨count,bound⟩
  let c : Barrier.Config n := ⟨cfg.cta,0,pc,cfg.nonempty⟩
  let r : Barrier.Request n := ⟨⟨cfg.cta,0,generation,pc⟩,t⟩
  let start := roundPrefix s pc generation count
  have ne : count ≠ n := by omega
  have hc : barrierConfig cfg start t = c := by
    simp [barrierConfig,start,roundPrefix,ne,pcs,c]
    split <;> rfl
  have hr : barrierRequest cfg start t 0 = r := by
    simp [barrierRequest,start,roundPrefix,ne,pcs,r,Barrier.prefixState]
  have hb : start.barrier = Barrier.prefixState generation count := by simp [start,roundPrefix,ne]
  have fresh : Barrier.Runnable (Barrier.prefixState generation count) t := by
    simp [Barrier.Runnable,Barrier.prefixState,t]
  have same : r.key = Barrier.key c (Barrier.prefixState generation count) := rfl
  have marked : Barrier.mark (Barrier.prefixState generation count) r.thread = Barrier.prefixState generation (count+1) :=
    Barrier.mark_prefix generation count bound
  refine ⟨synchronize cfg start t 0,?_,?_⟩
  · refine ⟨eligible,?_⟩
    have fresh' : start.barrier.arrived t = false := by rw [hb]; exact fresh
    simp only [start,roundPrefix,ne,↓reduceIte] at fresh' ⊢
    simp only [live,Bool.false_eq_true,↓reduceIte,Barrier.prefixState,lt_self_iff_false,decide_false,pcs,fetch]
    exact Dispatch.sync
  · by_cases last : count+1=n
    · have complete : Barrier.Complete (Barrier.mark (Barrier.prefixState generation count) r.thread) := by
        rw [marked,Barrier.complete_prefix_iff c]; omega
      have step := Barrier.completing_step c (Barrier.prefixState generation count) r same fresh complete
      simp only [synchronize,hc,hr,hb,step]
      simp [start,roundPrefix,ne,last,afterRound,Barrier.prefixState]
    · have incomplete : ¬Barrier.Complete (Barrier.mark (Barrier.prefixState generation count) r.thread) := by
        rw [marked,Barrier.complete_prefix_iff c]; omega
      have step := Barrier.waiting_step c (Barrier.prefixState generation count) r same fresh incomplete
      simp only [synchronize,hc,hr,hb,step]
      simp [start,roundPrefix,ne,last,marked,c]

theorem runs_append (first : Runs cfg program s left middle) (second : Runs cfg program middle right final) :
    Runs cfg program s (left++right) final := by
  induction first with
  | nil => exact second
  | cons step _ ih => simpa [List.append_assoc] using Runs.cons step (ih second)

/-- Every thread actually fetches the barrier at `pc`; increasing thread order
provides a finite witness. No fairness assumption is used. -/
theorem barrier_round_exists (cfg : Config n) (s : State n) (program : List Instr)
    (pc generation : Nat) (pcs : ∀ t, (s.lanes t).scalar.pc = pc)
    (live : ∀ t, (s.lanes t).halted = false) (reset : s.barrier = Barrier.reset generation)
    (site : s.site = none) (fetch : program[pc]? = some (.sync 0))
    (eligible : Mixed.Eligible cfg.target) :
    ∃ events, Runs cfg program s events (afterRound s generation) := by
  have base : roundPrefix s pc generation 0 = s := by
    have ne : 0 ≠ n := by have := cfg.nonempty; omega
    simp [roundPrefix,ne,Barrier.prefix_zero,← reset,← site]
  have witness : ∀ count, count ≤ n → ∃ events, Runs cfg program s events (roundPrefix s pc generation count) := by
    intro count bound
    induction count with
    | zero => exact ⟨[],by rw [base]; exact Runs.nil⟩
    | succ count ih =>
      obtain ⟨events,run⟩ := ih (by omega)
      obtain ⟨out,step,next⟩ := prefix_dispatch cfg s program pc generation count (by omega) pcs live fetch eligible
      have one : Runs cfg program (roundPrefix s pc generation count) out.events (roundPrefix s pc generation (count+1)) := by
        simpa only [List.append_nil,next] using Runs.cons step (Runs.nil (s := out.state))
      exact ⟨events++out.events,runs_append run one⟩
  simpa [roundPrefix] using witness n (Nat.le_refl n)

/-- The same resource can be fetched at two successive sites with different
barrier generations. Registers and both memory arenas are preserved. -/
theorem two_barriers_exist (cfg : Config n) (s : State n)
    (pcs : ∀ t, (s.lanes t).scalar.pc = 0) (live : ∀ t, (s.lanes t).halted = false)
    (reset : s.barrier = Barrier.reset 0) (site : s.site = none) (eligible : Mixed.Eligible cfg.target) :
    ∃ events, Runs cfg [.sync 0,.sync 0,.exit] s events (afterRound (afterRound s 0) 1) := by
  obtain ⟨first,run1⟩ := barrier_round_exists cfg s [.sync 0,.sync 0,.exit] 0 0 pcs live reset site rfl eligible
  obtain ⟨second,run2⟩ := barrier_round_exists cfg (afterRound s 0) [.sync 0,.sync 0,.exit] 1 1
    (by intro t; simp [afterRound,pcs]) live rfl rfl rfl eligible
  exact ⟨first++second,runs_append run1 run2⟩

end Ptx.Scalar.Parallel

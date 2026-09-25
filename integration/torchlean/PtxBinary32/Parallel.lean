import PtxBinary32.Mixed
import Ptx.Barrier

/-! A fetched mixed integer/binary32 machine for one cooperating thread array.
Global and CTA-owned shared arenas are distinct. Load candidates remain free;
completed-program memory admission is a separate graph obligation. -/
namespace Ptx.Scalar.Parallel

inductive Space where
  | global | shared
  deriving DecidableEq, Repr

inductive Instr where
  | localStep (instruction : Scalar.Instr)
  | memory (space : Space) (instruction : Scalar.Instr)
  | binary32 (instruction : Scalar.Binary32.Instr)
  | sync (resource : Fin 16)
  | exit
  deriving DecidableEq, Repr

structure Config (n : Nat) where
  target : Target
  cta : Nat
  nonempty : 0 < n

structure Lane where
  scalar : Scalar.State
  halted : Bool

structure State (n : Nat) where
  lanes : Fin n → Lane
  global : List Word
  shared : List Word
  barrier : Barrier.State n
  site : Option Nat

inductive Event (n : Nat) where
  | scalar (thread : Fin n) (space : Option Space) (event : Scalar.Occurrence)
  | binary32 (thread : Fin n) (event : Scalar.Binary32.Occurrence)
  | barrier (event : Barrier.Event n)
  | exit (thread : Fin n) (pc : Nat)

inductive Status where
  | advanced | waiting | released | halted | invalidPC | rejectedBarrier
  | fault (reason : Scalar.Fault) | unsupported (spelling : String)
  deriving DecidableEq, Repr

structure Outcome (n : Nat) where
  state : State n
  status : Status
  events : List (Event n)

def setLane (s : State n) (thread : Fin n) (lane : Lane) : State n :=
  {s with lanes := Function.update s.lanes thread lane}

def arena (s : State n) : Option Space → List Word
  | none => []
  | some .global => s.global
  | some .shared => s.shared

def scalarStep (candidate : Option Word) (thread : Fin n) (space : Option Space)
    (i : Scalar.Instr) (s : State n) : Outcome n :=
  let lane := s.lanes thread
  let input := {lane.scalar with memory := arena s space}
  match Scalar.eval candidate i input with
  | .next next event =>
    let installed := setLane s thread {lane with scalar := next}
    let final := match space with
      | none => installed
      | some .global => {installed with global := next.memory}
      | some .shared => {installed with shared := next.memory}
    ⟨final,.advanced,[.scalar thread space event]⟩
  | .halted next event =>
    ⟨setLane s thread {scalar := next,halted := true},.halted,[.scalar thread space event]⟩
  | .fault fault => ⟨s,.fault fault,[]⟩
  | .unsupported spelling => ⟨s,.unsupported spelling,[]⟩

/-- The first arrival fixes the site for this generation. Later arrivals at a
wrong site or resource are rejected; completion clears the site for reuse. -/
def barrierConfig (cfg : Config n) (s : State n) (thread : Fin n) : Barrier.Config n :=
  ⟨cfg.cta,0,s.site.getD (s.lanes thread).scalar.pc,cfg.nonempty⟩

def barrierRequest (cfg : Config n) (s : State n) (thread : Fin n) (resource : Fin 16) : Barrier.Request n :=
  ⟨⟨cfg.cta,resource,s.barrier.generation,(s.lanes thread).scalar.pc⟩,thread⟩

def synchronize (cfg : Config n) (s : State n) (thread : Fin n) (resource : Fin 16) : Outcome n :=
  let config := barrierConfig cfg s thread
  let request := barrierRequest cfg s thread resource
  let result := Barrier.step config s.barrier request
  match result.disposition with
  | .rejectedWrongKey => ⟨s,.rejectedBarrier,[]⟩
  | .waiting =>
    ⟨{s with barrier := result.state,site := some config.site},.waiting,result.events.map .barrier⟩
  | .released =>
    ⟨{s with barrier := result.state,site := none,lanes := fun t =>
      {s.lanes t with scalar := {(s.lanes t).scalar with pc := (s.lanes t).scalar.pc+1}}},
      .released,result.events.map .barrier⟩

inductive Dispatch (cfg : Config n) (candidate : Option Word) (thread : Fin n) : Instr → State n → Outcome n → Prop
  | localStep : Dispatch cfg candidate thread (.localStep i) s (scalarStep candidate thread none i s)
  | memory : Dispatch cfg candidate thread (.memory space i) s (scalarStep candidate thread (some space) i s)
  | binary32 : Scalar.Binary32.Eval i (s.lanes thread).scalar next event →
      Dispatch cfg candidate thread (.binary32 i) s
        ⟨setLane s thread {s.lanes thread with scalar := next},.advanced,[.binary32 thread event]⟩
  | sync : Dispatch cfg candidate thread (.sync resource) s (synchronize cfg s thread resource)
  | exit : Dispatch cfg candidate thread .exit s
      ⟨setLane s thread {s.lanes thread with halted := true},.halted,[.exit thread (s.lanes thread).scalar.pc]⟩

/-- Waiting threads cannot fetch past the barrier. The program is common to the
whole group; all thread-specific inputs are in registers and addresses. -/
def Step (cfg : Config n) (program : List Instr) (candidate : Option Word) (thread : Fin n)
    (s : State n) (outcome : Outcome n) : Prop :=
  Mixed.Eligible cfg.target ∧
  if (s.lanes thread).halted then outcome = ⟨s,.halted,[]⟩
  else if s.barrier.arrived thread then outcome = ⟨s,.waiting,[]⟩
  else match program[(s.lanes thread).scalar.pc]? with
    | none => outcome = ⟨s,.invalidPC,[]⟩
    | some i => Dispatch cfg candidate thread i s outcome

inductive Runs (cfg : Config n) (program : List Instr) : State n → List (Event n) → State n → Prop
  | nil : Runs cfg program s [] s
  | cons : Step cfg program candidate thread s outcome → Runs cfg program outcome.state rest final →
      Runs cfg program s (outcome.events ++ rest) final

theorem dispatch_exists (cfg : Config n) (candidate : Option Word) (thread : Fin n) (i : Instr) (s : State n) :
    ∃ out, Dispatch cfg candidate thread i s out := by
  cases i with
  | localStep i => exact ⟨_,.localStep⟩
  | memory space i => exact ⟨_,.memory⟩
  | binary32 i => obtain ⟨next,event,h⟩ := Scalar.Binary32.eval_exists i (s.lanes thread).scalar; exact ⟨_,.binary32 h⟩
  | sync r => exact ⟨_,.sync⟩
  | exit => exact ⟨_,.exit⟩

theorem step_exists (cfg : Config n) (program : List Instr) (candidate : Option Word) (thread : Fin n)
    (s : State n) (eligible : Mixed.Eligible cfg.target) : ∃ out, Step cfg program candidate thread s out := by
  unfold Step
  cases h : (s.lanes thread).halted
  · cases hwait : s.barrier.arrived thread
    · cases fetch : program[(s.lanes thread).scalar.pc]? with
      | none => exact ⟨_,eligible,rfl⟩
      | some i => obtain ⟨out,ho⟩ := dispatch_exists cfg candidate thread i s; exact ⟨out,eligible,ho⟩
    · exact ⟨_,eligible,rfl⟩
  · exact ⟨_,eligible,rfl⟩

theorem waiting_blocks (step : Step cfg program candidate thread s out)
    (waiting : s.barrier.arrived thread = true) (live : (s.lanes thread).halted = false) :
    out = ⟨s,.waiting,[]⟩ := by simpa [Step,waiting,live] using step.2

theorem fetch_origin (step : Step cfg program candidate thread s out)
    (live : (s.lanes thread).halted = false) (runnable : s.barrier.arrived thread = false)
    (valid : out.status ≠ .invalidPC) :
    ∃ i, program[(s.lanes thread).scalar.pc]? = some i ∧ Dispatch cfg candidate thread i s out := by
  have h := step.2
  simp only [live,runnable,Bool.false_eq_true,↓reduceIte] at h
  cases fetch : program[(s.lanes thread).scalar.pc]? with
  | none => simp [fetch] at h; exact False.elim (valid (h ▸ rfl))
  | some i => exact ⟨i,rfl,by simpa [fetch] using h⟩

/-- Waiters retain the common instruction site. Reset states establish this
invariant, and every fetched step preserves it; dispatch does not assume it. -/
def Aligned (s : State n) : Prop :=
  ∀ t, s.barrier.arrived t = true → s.site = some (s.lanes t).scalar.pc

/-- A release genuinely requires every participant, with the current site. -/
theorem release_aligned (cfg : Config n) (s : State n) (thread : Fin n) (resource : Fin 16)
    (aligned : Aligned s)
    (released : (Barrier.step (barrierConfig cfg s thread) s.barrier
      (barrierRequest cfg s thread resource)).disposition = .released) :
    ∀ t, (s.lanes t).scalar.pc = (s.lanes thread).scalar.pc := by
  obtain ⟨same,fresh,complete⟩ := (Barrier.released_iff _ _ _).mp released
  have siteEq := congrArg Barrier.Key.site same
  change (s.lanes thread).scalar.pc = s.site.getD (s.lanes thread).scalar.pc at siteEq
  intro t
  by_cases eq : t = thread
  · subst t; rfl
  have ht := complete t
  have arrived : s.barrier.arrived t = true := by simpa [Barrier.Waiting,Barrier.mark,barrierRequest,eq] using ht
  have hs := aligned t arrived
  rw [hs] at siteEq
  exact siteEq.symm

@[simp] theorem reset_aligned (lanes : Fin n → Lane) (global shared : List Word) (generation : Nat) :
    Aligned (⟨lanes,global,shared,Barrier.reset generation,none⟩ : State n) := by
  intro t h; simp [Barrier.reset] at h

/-- Updating a runnable lane preserves the program-counter agreement of waiters. -/
theorem setLane_aligned (aligned : Aligned s) (fresh : s.barrier.arrived thread = false)
    (lane : Lane) : Aligned (setLane s thread lane) := by
  intro t ht
  have different : t ≠ thread := by intro eq; subst t; simp [setLane,fresh] at ht
  simpa [setLane,Function.update, different] using aligned t ht

/-- Barrier dispatch maintains alignment, including after resource reuse. -/
theorem synchronize_aligned (cfg : Config n) (s : State n) (thread : Fin n) (resource : Fin 16)
    (aligned : Aligned s) : Aligned (synchronize cfg s thread resource).state := by
  unfold synchronize
  generalize hc : barrierConfig cfg s thread = c
  generalize hr : barrierRequest cfg s thread resource = r
  have requestThread : r.thread = thread := by subst r; rfl
  by_cases same : r.key = Barrier.key c s.barrier
  · have siteEq : (s.lanes thread).scalar.pc = c.site := by
      have h := congrArg Barrier.Key.site same
      simpa [← hr,barrierRequest,Barrier.key] using h
    by_cases old : s.barrier.arrived r.thread = true
    · simp only [Barrier.step,same,old,↓reduceIte]
      intro t ht
      have hs := aligned t ht
      have current := aligned thread (requestThread ▸ old)
      have eq : (s.lanes t).scalar.pc = (s.lanes thread).scalar.pc := Option.some.inj (hs.symm.trans current)
      simp [← siteEq,eq]
    · by_cases complete : Barrier.Complete (Barrier.mark s.barrier r.thread)
      · simp only [Barrier.step,same,old,complete,↓reduceIte]
        intro t ht
        simp [Barrier.reset] at ht
      · simp only [Barrier.step,same,old,complete,↓reduceIte]
        intro t ht
        by_cases eq : t = thread
        · simp [eq,siteEq]
        · have previous : s.barrier.arrived t = true := by
            simpa [Barrier.mark,requestThread,eq] using ht
          have hs := aligned t previous
          have cfgSite : c.site = (s.lanes t).scalar.pc := by
            rw [← hc]; simp [barrierConfig,hs]
          simp [cfgSite]
  · simpa only [Barrier.step,same,↓reduceIte] using aligned

private theorem scalarStep_aligned {space : Option Space}
    (aligned : Aligned s) (fresh : s.barrier.arrived thread = false) :
    Aligned (scalarStep candidate thread space i s).state := by
  cases h : Scalar.eval candidate i {(s.lanes thread).scalar with memory := arena s space} with
  | next next event =>
    cases space with
    | none => simpa only [scalarStep,h] using setLane_aligned aligned fresh {s.lanes thread with scalar := next}
    | some space => cases space <;> simpa only [scalarStep,h,Aligned,setLane] using setLane_aligned aligned fresh {s.lanes thread with scalar := next}
  | halted next event => simpa only [scalarStep,h] using setLane_aligned aligned fresh (⟨next,true⟩ : Lane)
  | fault reason => simpa only [scalarStep,h] using aligned
  | unsupported spelling => simpa only [scalarStep,h] using aligned

theorem dispatch_aligned (h : Dispatch cfg candidate thread i s out)
    (aligned : Aligned s) (fresh : s.barrier.arrived thread = false) : Aligned out.state := by
  cases h with
  | localStep => exact scalarStep_aligned aligned fresh
  | memory => exact scalarStep_aligned aligned fresh
  | binary32 _ => exact setLane_aligned aligned fresh _
  | sync => exact synchronize_aligned _ _ _ _ aligned
  | exit => exact setLane_aligned aligned fresh _

theorem step_aligned (step : Step cfg program candidate thread s out) (aligned : Aligned s) :
    Aligned out.state := by
  have h := step.2
  split at h
  · subst out; exact aligned
  · split at h
    · subst out; exact aligned
    · split at h
      · subst out; exact aligned
      · exact dispatch_aligned h aligned (by simpa using ‹¬s.barrier.arrived thread = true›)

theorem runs_aligned (run : Runs cfg program s events final) (aligned : Aligned s) : Aligned final := by
  induction run with
  | nil => exact aligned
  | cons step _ ih => exact ih (step_aligned step aligned)

/-- Successful accesses are four-byte aligned and inside the selected arena.
This is an extent check; allocation permissions and initialization are separate. -/
def AccessSafe (s : State n) : Event n → Prop
  | .scalar _ space event => ∀ effect, event.memory = some effect →
      Scalar.ValidAddress (arena s space) effect.address
  | _ => True

def OutcomeSafe (s : State n) (out : Outcome n) : Prop :=
  out.state.global.length = s.global.length ∧ out.state.shared.length = s.shared.length ∧
    ∀ event ∈ out.events, AccessSafe s event

theorem scalarStep_safe (s : State n) (thread : Fin n) (space : Option Space)
    (i : Scalar.Instr) (candidate : Option Word) : OutcomeSafe s (scalarStep candidate thread space i s) := by
  cases h : Scalar.eval candidate i {(s.lanes thread).scalar with memory := arena s space} with
  | next next event =>
    have length := Scalar.eval_memory_length h
    have safe : ∀ effect, event.memory = some effect → Scalar.ValidAddress (arena s space) effect.address := fun _ he => Scalar.eval_memory_safe h he
    cases space with
    | none => simpa [OutcomeSafe,scalarStep,h,setLane,AccessSafe] using safe
    | some space =>
      cases space <;> simp only [scalarStep,h]
      all_goals simpa [OutcomeSafe,setLane,AccessSafe,arena] using And.intro length safe
  | halted next event =>
    have noMemory := (Scalar.eval_halted h).2
    simp [OutcomeSafe,scalarStep,h,setLane,AccessSafe,noMemory]
  | fault reason => simp [OutcomeSafe,scalarStep,h]
  | unsupported spelling => simp [OutcomeSafe,scalarStep,h]

theorem synchronize_safe (cfg : Config n) (s : State n) (thread : Fin n) (resource : Fin 16) :
    OutcomeSafe s (synchronize cfg s thread resource) := by
  cases h : (Barrier.step (barrierConfig cfg s thread) s.barrier (barrierRequest cfg s thread resource)).disposition <;>
    simp [synchronize,h,OutcomeSafe,AccessSafe]

theorem dispatch_safe (h : Dispatch cfg candidate thread i s out) : OutcomeSafe s out := by
  cases h with
  | localStep => exact scalarStep_safe _ _ _ _ _
  | memory => exact scalarStep_safe _ _ _ _ _
  | binary32 _ => simp [OutcomeSafe,setLane,AccessSafe]
  | sync => exact synchronize_safe _ _ _ _
  | exit => simp [OutcomeSafe,setLane,AccessSafe]

theorem step_safe (step : Step cfg program candidate thread s out) : OutcomeSafe s out := by
  have h := step.2
  split at h
  · subst out; simp [OutcomeSafe]
  · split at h
    · subst out; simp [OutcomeSafe]
    · split at h
      · subst out; simp [OutcomeSafe]
      · exact dispatch_safe h

theorem runs_memory_length (run : Runs cfg program s events final) :
    final.global.length = s.global.length ∧ final.shared.length = s.shared.length := by
  induction run with
  | nil => exact ⟨rfl,rfl⟩
  | cons step _ ih => exact ⟨ih.1.trans (step_safe step).1,ih.2.trans (step_safe step).2.1⟩

private theorem accessSafe_extent (hg : s'.global.length = s.global.length)
    (hs : s'.shared.length = s.shared.length) (safe : AccessSafe s' event) : AccessSafe s event := by
  cases event with
  | scalar thread space event =>
    cases space with
    | none => exact safe
    | some space => cases space <;> simpa [AccessSafe,Scalar.ValidAddress,arena,hg,hs] using safe
  | _ => trivial

/-- All emitted accesses remain inside the original arenas, even in prefixes
that later fault or get stuck. This does not establish successful termination. -/
theorem runs_access_safe {s final : State n} {events : List (Event n)} (run : Runs cfg program s events final) (event : Event n) (member : event ∈ events) :
    AccessSafe s event := by
  induction run with
  | nil => simp at member
  | cons step _ ih =>
    rcases List.mem_append.mp member with current | later
    · exact (step_safe step).2.2 event current
    · exact accessSafe_extent (step_safe step).1 (step_safe step).2.1 (ih later)

end Ptx.Scalar.Parallel

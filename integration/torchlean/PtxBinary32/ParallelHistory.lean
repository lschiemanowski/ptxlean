import PtxBinary32.ParallelBarrier
import Ptx.CollectiveOrder

/-! The barrier's control-order certificate is derived from emitted instruction
history. No read value or desired kernel output is an invariant premise. -/
namespace Ptx.Scalar.Parallel.History

def activeKey (cfg : Config n) (s : State n) : Barrier.Key :=
  ⟨cfg.cta,0,s.barrier.generation,s.site.getD 0⟩

/-- Every current waiter has a real arrival in the accumulated history. -/
def WaitingOrigin (cfg : Config n) (s : State n) (history : List (Event n)) : Prop :=
  ∀ t, s.barrier.arrived t = true → .barrier (.arrival (activeKey cfg s) t) ∈ history

def CompleteOrigins (history : List (Event n)) : Prop :=
  ∀ (c : Nat) (key : Barrier.Key), history[c]? = some (.barrier (.completion key)) →
    ∀ t : Fin n, ∃ a : Nat, a < c ∧ history[a]? = some (.barrier (.arrival key t))

def FreshCompletions (before added : List (Event n)) : Prop :=
  ∀ c key, added[c]? = some (.barrier (.completion key)) →
    ∀ t, ∃ a, a < before.length+c ∧
      (before++added)[a]? = some (.barrier (.arrival key t))

private theorem waiting_append {cfg : Config n} {s : State n} {before : List (Event n)} (h : WaitingOrigin cfg s before) (added : List (Event n)) :
    WaitingOrigin cfg s (before++added) := by
  intro t ht
  exact List.mem_append_left _ (h t ht)

private theorem fresh_empty (before : List (Event n)) : FreshCompletions before [] := by
  intro c key h; simp at h

private theorem fresh_single (before : List (Event n)) (e : Event n)
    (noCompletion : ∀ key, e ≠ .barrier (.completion key)) : FreshCompletions before [e] := by
  intro c key h
  cases c with
  | zero => simp only [List.getElem?_cons_zero,Option.some.injEq] at h; exact False.elim (noCompletion key h)
  | succ c => simp at h

private theorem fresh_release (before : List (Event n)) (key : Barrier.Key) (selected : Fin n)
    (previous : ∀ t, t ≠ selected → .barrier (.arrival key t) ∈ before) :
    FreshCompletions before [.barrier (.arrival key selected),.barrier (.completion key)] := by
  intro c observed h t
  rcases c with _ | _ | c
  · simp at h
  · simp only [List.getElem?_cons_succ,List.getElem?_cons_zero,Option.some.injEq,Event.barrier.injEq,
      Barrier.Event.completion.injEq] at h
    subst observed
    by_cases same : t=selected
    · subst t
      exact ⟨before.length,by omega,by simp⟩
    · obtain ⟨a,bound,atIndex⟩ := List.mem_iff_getElem.mp (previous t same)
      exact ⟨a,by omega,by simp [List.getElem?_append,bound,atIndex]⟩
  · simp at h

private theorem append_complete (old : CompleteOrigins before) (new : FreshCompletions before added) :
    CompleteOrigins (before++added) := by
  intro c key atC t
  by_cases early : c < before.length
  · have hc : before[c]? = some (.barrier (.completion key)) := by
      simpa [List.getElem?_append,early] using atC
    obtain ⟨a,bound,atA⟩ := old c key hc t
    exact ⟨a,bound,by simpa only [List.getElem?_append,ite_eq_left (show a < before.length by omega)] using atA⟩
  · have hc : added[c-before.length]? = some (.barrier (.completion key)) := by
      simpa [List.getElem?_append,early] using atC
    obtain ⟨a,bound,atA⟩ := new _ key hc t
    exact ⟨a,by omega,atA⟩

private theorem key_of_waiter (cfg : Config n) (s : State n) (selected t : Fin n)
    (aligned : Aligned s) (waiting : s.barrier.arrived t = true) :
    Barrier.key (barrierConfig cfg s selected) s.barrier = activeKey cfg s := by
  simp [Barrier.key,barrierConfig,activeKey,aligned t waiting]

private theorem synchronize_history (cfg : Config n) (s : State n) (thread : Fin n) (resource : Fin 16)
    (before : List (Event n)) (aligned : Aligned s) (origin : WaitingOrigin cfg s before) :
    WaitingOrigin cfg (synchronize cfg s thread resource).state
      (before++(synchronize cfg s thread resource).events) ∧
    FreshCompletions before (synchronize cfg s thread resource).events := by
  let c := barrierConfig cfg s thread
  let r := barrierRequest cfg s thread resource
  by_cases same : r.key = Barrier.key c s.barrier
  · by_cases old : s.barrier.arrived r.thread = true
    · have site : some c.site = s.site := by simp [c,barrierConfig,aligned thread old]
      simpa only [synchronize,show barrierConfig cfg s thread = c from rfl,
        show barrierRequest cfg s thread resource = r from rfl,Barrier.step,same,old,Bool.false_eq_true,↓reduceIte,
        site,List.map_nil,List.append_nil] using And.intro origin (fresh_empty before)
    · by_cases complete : Barrier.Complete (Barrier.mark s.barrier r.thread)
      · have previous : ∀ t, t ≠ thread → .barrier (.arrival r.key t) ∈ before := by
          intro t different
          have arrived : s.barrier.arrived t = true := by
            simpa [Barrier.Waiting,Barrier.mark,r,barrierRequest,different] using complete t
          have keys := same.trans (key_of_waiter cfg s thread t aligned arrived)
          exact keys ▸ origin t arrived
        constructor
        · intro t ht
          simp [synchronize,← show c = barrierConfig cfg s thread from rfl,
            ← show r = barrierRequest cfg s thread resource from rfl,Barrier.step,same,old,Bool.false_eq_true,complete,Barrier.reset] at ht
        · simpa only [synchronize,show barrierConfig cfg s thread = c from rfl,
            show barrierRequest cfg s thread resource = r from rfl,Barrier.step,same,old,Bool.false_eq_true,complete,↓reduceIte,
            List.map_cons,List.map_nil] using fresh_release before r.key r.thread previous
      · have nextKey : activeKey cfg {s with barrier := Barrier.mark s.barrier r.thread,site := some c.site} = r.key := by
          rw [same]; rfl
        constructor
        · simp only [synchronize,show barrierConfig cfg s thread = c from rfl,
            show barrierRequest cfg s thread resource = r from rfl,Barrier.step,same,old,Bool.false_eq_true,complete,↓reduceIte,
            List.map_cons,List.map_nil]
          intro t ht
          rw [nextKey]
          by_cases selected : t=thread
          · subst t; exact List.mem_append_right _ (by simp [same,show r.thread = thread from rfl])
          · have arrived : s.barrier.arrived t = true := by simpa [Barrier.mark,r,barrierRequest,selected] using ht
            have keys := same.trans (key_of_waiter cfg s thread t aligned arrived)
            exact List.mem_append_left _ (keys ▸ origin t arrived)
        · simpa only [synchronize,show barrierConfig cfg s thread = c from rfl,
            show barrierRequest cfg s thread resource = r from rfl,Barrier.step,same,old,Bool.false_eq_true,complete,↓reduceIte,
            List.map_cons,List.map_nil] using fresh_single before (.barrier (.arrival r.key r.thread)) (by intro key; simp)
  · simpa only [synchronize,show barrierConfig cfg s thread = c from rfl,
      show barrierRequest cfg s thread resource = r from rfl,Barrier.step,same,↓reduceIte,List.append_nil] using
      And.intro origin (fresh_empty before)

private theorem ordinary_history {cfg : Config n} {s : State n} {before : List (Event n)}
    (out : Outcome n) (origin : WaitingOrigin cfg s before)
    (barrier : out.state.barrier = s.barrier) (site : out.state.site = s.site)
    (noCompletion : ∀ key, .barrier (.completion key) ∉ out.events) :
    WaitingOrigin cfg out.state (before++out.events) ∧ FreshCompletions before out.events := by
  constructor
  · simpa only [WaitingOrigin,activeKey,barrier,site] using waiting_append origin out.events
  · intro c key atC
    exact False.elim (noCompletion key (List.mem_of_getElem? atC))

private theorem scalar_history (cfg : Config n) (s : State n) (thread : Fin n) (space : Option Space)
    (i : Scalar.Instr) (candidate : Option Word) (before : List (Event n))
    (origin : WaitingOrigin cfg s before) :
    WaitingOrigin cfg (scalarStep candidate thread space i s).state
      (before++(scalarStep candidate thread space i s).events) ∧
    FreshCompletions before (scalarStep candidate thread space i s).events := by
  apply ordinary_history (scalarStep candidate thread space i s) origin
  all_goals
    cases h : Scalar.eval candidate i {(s.lanes thread).scalar with memory := arena s space} with
    | next next event =>
      cases space with
      | none => simp [scalarStep,h,setLane]
      | some space => cases space <;> simp [scalarStep,h,setLane]
    | halted next event => simp [scalarStep,h,setLane]
    | fault reason => simp [scalarStep,h]
    | unsupported spelling => simp [scalarStep,h]

private theorem dispatch_history {cfg : Config n} {s : State n} {before : List (Event n)}
    (step : Dispatch cfg candidate thread i s out) (aligned : Aligned s)
    (origin : WaitingOrigin cfg s before) :
    WaitingOrigin cfg out.state (before++out.events) ∧ FreshCompletions before out.events := by
  cases step with
  | localStep => exact scalar_history _ _ _ _ _ _ _ origin
  | memory => exact scalar_history _ _ _ _ _ _ _ origin
  | binary32 _ =>
    apply ordinary_history
    · exact origin
    · rfl
    · rfl
    · intro key; simp
  | sync => exact synchronize_history _ _ _ _ _ aligned origin
  | exit =>
    apply ordinary_history
    · exact origin
    · rfl
    · rfl
    · intro key; simp

theorem step_history {cfg : Config n} {s : State n} {before : List (Event n)}
    (step : Step cfg program candidate thread s out) (aligned : Aligned s)
    (origin : WaitingOrigin cfg s before) :
    WaitingOrigin cfg out.state (before++out.events) ∧ FreshCompletions before out.events := by
  have h := step.2
  split at h
  · subst out; apply ordinary_history _ origin <;> simp
  · split at h
    · subst out; apply ordinary_history _ origin <;> simp
    · split at h
      · subst out; apply ordinary_history _ origin <;> simp
      · exact dispatch_history h aligned origin

theorem runs_history {cfg : Config n} {s : State n} {before : List (Event n)}
    (run : Runs cfg program s events final) (aligned : Aligned s)
    (origin : WaitingOrigin cfg s before) (complete : CompleteOrigins before) :
    WaitingOrigin cfg final (before++events) ∧ CompleteOrigins (before++events) := by
  induction run generalizing before with
  | nil => simpa using And.intro origin complete
  | cons step _ ih =>
    obtain ⟨nextOrigin,newCompletions⟩ := step_history step aligned origin
    have result := ih (step_aligned step aligned) nextOrigin (append_complete complete newCompletions)
    simpa only [List.append_assoc] using result

/-- Every observed completion in an arbitrary candidate run from a reset barrier
has earlier actual arrivals from all participants at exactly its phase key. -/
theorem completed_arrivals {cfg : Config n} {s : State n}
    (run : Runs cfg program s events final) (reset : s.barrier = Barrier.reset generation) :
    CompleteOrigins events := by
  have aligned : Aligned s := by intro t ht; simp [reset,Barrier.reset] at ht
  have origin : WaitingOrigin cfg s [] := by intro t ht; simp [reset,Barrier.reset] at ht
  have complete : CompleteOrigins ([] : List (Event n)) := by intro c key h; simp at h
  simpa using (runs_history run aligned origin complete).2

/-- A phase is an observed completion, not a caller-supplied barrier annotation. -/
structure Phase (events : List (Event n)) where
  position : Nat
  key : Barrier.Key
  observed : events[position]? = some (.barrier (.completion key))

noncomputable def arrivalPosition {events : List (Event n)} (complete : CompleteOrigins events)
    (phase : Phase events) (thread : Fin n) : Nat :=
  Classical.choose (complete phase.position phase.key phase.observed thread)

theorem arrival_position_spec {events : List (Event n)} (complete : CompleteOrigins events)
    (phase : Phase events) (thread : Fin n) :
    arrivalPosition complete phase thread < phase.position ∧
      events[arrivalPosition complete phase thread]? = some (.barrier (.arrival phase.key thread)) :=
  Classical.choose_spec (complete phase.position phase.key phase.observed thread)

/-- Initial-memory labels have no issuing thread and do not participate.
The factors of three distinguish completion from abstract resumption without
adding a fictitious instruction or a second memory event. -/
noncomputable def certificate {events : List (Event n)} (complete : CompleteOrigins events)
    (owner : Memory → Option (Fin n)) (position : Memory → Nat) :
    CollectiveOrder.Certificate Memory (Option (Fin n)) (Phase events) where
  owner := owner
  participates := fun _ t => t.isSome
  memoryPos := fun e => 3*position e
  arrivalPos := fun p t => match t with | none => 0 | some t => 3*arrivalPosition complete p t
  completionPos := fun p => 3*p.position+1
  resumePos := fun p _ => 3*p.position+2
  arrival_before_completion := by
    intro p t ht
    cases t with
    | none => simp at ht
    | some t => have := (arrival_position_spec complete p t).1; dsimp; omega
  completion_before_resume := by intro p t _; omega

theorem before_certificate {events : List (Event n)} (complete : CompleteOrigins events)
    (owner : Memory → Option (Fin n)) (position : Memory → Nat) (e : Memory) (p : Phase events) (t : Fin n)
    (issuer : owner e = some t) (before : position e < arrivalPosition complete p t) :
    (certificate complete owner position).Before e p (some t) := by
  refine ⟨issuer,rfl,?_⟩
  change 3*position e < 3*arrivalPosition complete p t
  omega

theorem after_certificate {events : List (Event n)} (complete : CompleteOrigins events)
    (owner : Memory → Option (Fin n)) (position : Memory → Nat) (e : Memory) (p : Phase events) (t : Fin n)
    (issuer : owner e = some t) (after : p.position < position e) :
    (certificate complete owner position).After e p (some t) := by
  refine ⟨issuer,rfl,?_⟩
  change 3*p.position+2 < 3*position e
  omega

end Ptx.Scalar.Parallel.History

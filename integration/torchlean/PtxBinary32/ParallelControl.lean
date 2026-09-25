import PtxBinary32.ParallelHistory

/-! Instruction order for arbitrary candidate executions of straight-line
programs. Read candidates and binary32 result choices remain unrestricted.
Waiting/halting consumes the current site; release advances every participant. -/
namespace Ptx.Scalar.Parallel.Control

def StraightOp : Scalar.Op → Prop
  | .bra _ | .exit => False
  | _ => True

def StraightInstr : Instr → Prop
  | .localStep i | .memory _ i => StraightOp i.op
  | _ => True

def Straight (program : List Instr) : Prop := ∀ i ∈ program, StraightInstr i

/-- Completion has no single issuer; all other events record a thread and PC. -/
def stamp : Event n → Option (Fin n × Nat)
  | .scalar t _ e => some (t,e.pc)
  | .binary32 t e => some (t,e.pc)
  | .barrier (.arrival key t) => some (t,key.site)
  | .barrier (.completion _) => none
  | .exit t pc => some (t,pc)

/-- A proof measure, not a new machine state or scheduling restriction. -/
def cursor (s : State n) (t : Fin n) : Nat :=
  2*(s.lanes t).scalar.pc + if (s.lanes t).halted || s.barrier.arrived t then 1 else 0

theorem cursor_bounds (s : State n) (t : Fin n) :
    2*(s.lanes t).scalar.pc ≤ cursor s t ∧ cursor s t ≤ 2*(s.lanes t).scalar.pc+1 := by
  unfold cursor; split <;> omega

structure Progress (s : State n) (out : Outcome n) : Prop where
  monotone : ∀ t, cursor s t ≤ cursor out.state t
  emitted : ∀ (pos : Nat) e t pc, out.events[pos]? = some e → stamp e = some (t,pc) →
    cursor s t = 2*pc ∧ 2*pc < cursor out.state t
  unique : ∀ (p q : Nat) e f t u pc qc, out.events[p]? = some e → out.events[q]? = some f →
    stamp e = some (t,pc) → stamp f = some (u,qc) → p=q

private theorem idle (s : State n) (status : Status) : Progress s ⟨s,status,[]⟩ where
  monotone := fun _ => Nat.le_refl _
  emitted := by intros; simp_all
  unique := by intros; simp_all

private theorem single {s : State n} {out : Outcome n} {selected : Fin n} {pc : Nat} {event : Event n}
    (events : out.events = [event]) (tag : stamp event = some (selected,pc))
    (before : cursor s selected = 2*pc) (after : 2*pc < cursor out.state selected)
    (mono : ∀ t, cursor s t ≤ cursor out.state t) : Progress s out where
  monotone := mono
  emitted := by
    intro pos e t qc atPos tagged
    rw [events] at atPos
    have pos0 : pos=0 := by cases pos <;> simp_all
    subst pos
    have eq : e=event := by simpa using atPos.symm
    subst e
    have pair := Option.some.inj (tag.symm.trans tagged)
    cases pair
    exact ⟨before,after⟩
  unique := by
    intro p q e f t u pc qc hp hq _ _
    have p0 : p=0 := by rw [events] at hp; cases p <;> simp_all
    have q0 : q=0 := by rw [events] at hq; cases q <;> simp_all
    omega

private theorem scalar_next (i : Scalar.Instr) (s next : Scalar.State) (event : Scalar.Occurrence)
    (straight : StraightOp i.op) (evaluated : Scalar.eval candidate i s = .next next event) :
    next.pc=s.pc+1 ∧ event.pc=s.pc := by
  rcases i with ⟨guard,op⟩
  cases op <;> simp only [StraightOp] at straight
  all_goals first | contradiction | skip
  all_goals cases enabled : guard.eval s <;> simp only [Scalar.eval,enabled,↓reduceIte] at evaluated
  all_goals first
    | (obtain ⟨rfl,rfl⟩ := Scalar.StepResult.next.inj evaluated; exact ⟨rfl,rfl⟩)
    | contradiction
    | (split at evaluated; contradiction; obtain ⟨rfl,rfl⟩ := Scalar.StepResult.next.inj evaluated; exact ⟨rfl,rfl⟩)

private theorem scalar_not_halted (i : Scalar.Instr) (s next : Scalar.State) (event : Scalar.Occurrence)
    (straight : StraightOp i.op) : Scalar.eval candidate i s ≠ .halted next event := by
  rcases i with ⟨guard,op⟩
  cases op <;> simp only [StraightOp] at straight
  all_goals cases enabled : guard.eval s <;> simp only [Scalar.eval,enabled,↓reduceIte]
  all_goals first | (solve | simp) | (split <;> simp)

private theorem advance (s : State n) (t : Fin n) (next : Scalar.State)
    (pc : next.pc = (s.lanes t).scalar.pc+1)
    (live : (s.lanes t).halted = false) (fresh : s.barrier.arrived t = false) :
    cursor s t = 2*(s.lanes t).scalar.pc ∧
    2*(s.lanes t).scalar.pc < cursor (setLane s t {s.lanes t with scalar := next}) t ∧
    (∀ u, cursor s u ≤ cursor (setLane s t {s.lanes t with scalar := next}) u) := by
  have before : cursor s t = 2*(s.lanes t).scalar.pc := by simp [cursor,live,fresh]
  have after : cursor (setLane s t {s.lanes t with scalar := next}) t = 2*((s.lanes t).scalar.pc+1) := by
    simp [cursor,setLane,pc,live,fresh]
  refine ⟨before,by omega,?_⟩
  intro u
  by_cases eq : u=t
  · subst u; omega
  · simp [cursor,setLane,Function.update,eq]

private theorem scalar_progress (s : State n) (t : Fin n) (space : Option Space) (i : Scalar.Instr)
    (straight : StraightOp i.op) (live : (s.lanes t).halted = false) (fresh : s.barrier.arrived t = false) :
    Progress s (scalarStep candidate t space i s) := by
  cases ev : Scalar.eval candidate i {(s.lanes t).scalar with memory := arena s space} with
  | next next event =>
    have info := scalar_next i _ next event straight ev
    have adv := advance s t next info.1 live fresh
    cases space with
    | none =>
      simp only [scalarStep,ev]
      exact single rfl (by simp [stamp,info.2]) adv.1 adv.2.1 adv.2.2
    | some space =>
      cases space <;> simp only [scalarStep,ev]
      all_goals
        apply single rfl (by simp [stamp,info.2]) adv.1
        · exact adv.2.1
        · exact adv.2.2
  | halted next event => exact False.elim (scalar_not_halted i _ _ _ straight ev)
  | fault reason => simpa only [scalarStep,ev] using idle s (.fault reason)
  | unsupported spelling => simpa only [scalarStep,ev] using idle s (.unsupported spelling)

private theorem synchronize_progress (cfg : Config n) (s : State n) (t : Fin n) (resource : Fin 16)
    (live : (s.lanes t).halted = false) (fresh : s.barrier.arrived t = false) :
    Progress s (synchronize cfg s t resource) := by
  by_cases same : (barrierRequest cfg s t resource).key = Barrier.key (barrierConfig cfg s t) s.barrier
  · dsimp [barrierRequest] at same
    have keySite : (Barrier.key (barrierConfig cfg s t) s.barrier).site = (s.lanes t).scalar.pc :=
      (congrArg Barrier.Key.site same).symm
    by_cases complete : Barrier.Complete (Barrier.mark s.barrier t)
    · simp only [synchronize,Barrier.step,same,barrierRequest,fresh,Bool.false_eq_true,complete,
        ↓reduceIte,List.map_cons,List.map_nil]
      refine ⟨?_,?_,?_⟩
      · intro u
        have old := cursor_bounds s u
        unfold cursor
        dsimp
        split <;> omega
      · intro pos e u pc atPos tagged
        rcases pos with _ | _ | pos
        · simp only [List.getElem?_cons_zero,Option.some.injEq] at atPos
          subst e
          have eq : (t,(s.lanes t).scalar.pc)=(u,pc) := by simpa [stamp,keySite] using tagged
          cases eq
          constructor
          · simp [cursor,live,fresh]
          · simp [cursor,Barrier.reset,live]
        · simp only [List.getElem?_cons_succ,List.getElem?_cons_zero,Option.some.injEq] at atPos
          subst e; simp [stamp] at tagged
        · simp at atPos
      · intro p q e f u v pc qc hp hq he hf
        have p0 : p=0 := by
          rcases p with _ | _ | p
          · rfl
          · simp only [List.getElem?_cons_succ,List.getElem?_cons_zero,Option.some.injEq] at hp
            subst e; simp [stamp] at he
          · simp at hp
        have q0 : q=0 := by
          rcases q with _ | _ | q
          · rfl
          · simp only [List.getElem?_cons_succ,List.getElem?_cons_zero,Option.some.injEq] at hq
            subst f; simp [stamp] at hf
          · simp at hq
        omega
    · simp only [synchronize,Barrier.step,same,barrierRequest,fresh,Bool.false_eq_true,complete,
        ↓reduceIte,List.map_cons,List.map_nil]
      apply single rfl (by rfl)
      · simp [cursor,live,fresh,keySite]
      · simp [cursor,live,Barrier.mark,keySite]
      · intro u
        by_cases eq : u=t
        · subst u; simp [cursor,live,fresh,Barrier.mark]
        · simp [cursor,Barrier.mark,eq]
  · simpa only [synchronize,Barrier.step,same,↓reduceIte] using idle s .rejectedBarrier

theorem dispatch_progress (step : Dispatch cfg candidate t i s out)
    (straight : StraightInstr i) (live : (s.lanes t).halted = false) (fresh : s.barrier.arrived t = false) :
    Progress s out := by
  cases step with
  | localStep => exact scalar_progress _ _ _ _ straight live fresh
  | memory => exact scalar_progress _ _ _ _ straight live fresh
  | binary32 ev =>
    have adv := advance s t _ (Scalar.Binary32.eval_frame _ _ _ _ ev).1 live fresh
    apply single rfl ?_ adv.1 adv.2.1 adv.2.2
    rw [Scalar.Binary32.eval_event _ _ _ _ ev]; rfl
  | sync => exact synchronize_progress _ _ _ _ live fresh
  | exit =>
    apply single rfl rfl
    · simp [cursor,live,fresh]
    · simp [cursor,setLane]
    · intro u
      by_cases eq : u=t
      · subst u; simp [cursor,setLane,live,fresh]
      · simp [cursor,setLane,Function.update,eq]

theorem step_progress (step : Step cfg program candidate t s out) (straight : Straight program) :
    Progress s out := by
  have h := step.2
  split at h
  · subst out; exact idle _ _
  · split at h
    · subst out; exact idle _ _
    · split at h
      · subst out; exact idle _ _
      · exact dispatch_progress h (straight _ (List.mem_of_getElem? (by assumption)))
          (by simpa using ‹¬(s.lanes t).halted = true›)
          (by simpa using ‹¬s.barrier.arrived t = true›)

/-- Bounds and strict per-thread order for a whole, possibly unfinished trace. -/
structure TraceProgress (s : State n) (events : List (Event n)) (final : State n) : Prop where
  monotone : ∀ t, cursor s t ≤ cursor final t
  emitted : ∀ (pos : Nat) e t pc, events[pos]? = some e → stamp e = some (t,pc) →
    cursor s t ≤ 2*pc ∧ 2*pc < cursor final t
  ordered : ∀ (p q : Nat) e f t pc qc, p<q → events[p]? = some e → events[q]? = some f →
    stamp e = some (t,pc) → stamp f = some (t,qc) → pc<qc

theorem runs_progress (run : Runs cfg program s events final) (straight : Straight program) :
    TraceProgress s events final := by
  induction run with
  | nil => exact ⟨fun _ => Nat.le_refl _,by intros; simp_all,by intros; simp_all⟩
  | @cons candidate t s out rest final step run ih =>
    have now := step_progress step straight
    refine ⟨fun t => (now.monotone t).trans (ih.monotone t),?_,?_⟩
    · intro pos e t pc atPos tagged
      by_cases early : pos < out.events.length
      · have h : out.events[pos]? = some e := by simpa [List.getElem?_append,early] using atPos
        have bounds := now.emitted pos e t pc h tagged
        exact ⟨Nat.le_of_eq bounds.1,(bounds.2).trans_le (ih.monotone t)⟩
      · have h : rest[pos-out.events.length]? = some e := by simpa [List.getElem?_append,early] using atPos
        have bounds := ih.emitted _ e t pc h tagged
        exact ⟨(now.monotone t).trans bounds.1,bounds.2⟩
    · intro p q e f t pc qc earlier hp hq he hf
      by_cases pe : p < out.events.length
      · have atP : out.events[p]? = some e := by simpa [List.getElem?_append,pe] using hp
        by_cases qe : q < out.events.length
        · have atQ : out.events[q]? = some f := by simpa [List.getElem?_append,qe] using hq
          have := now.unique p q e f t t pc qc atP atQ he hf
          omega
        · have atQ : rest[q-out.events.length]? = some f := by simpa [List.getElem?_append,qe] using hq
          have first := (now.emitted p e t pc atP he).2
          have second := (ih.emitted _ f t qc atQ hf).1
          omega
      · have qe : ¬q < out.events.length := by omega
        have atP : rest[p-out.events.length]? = some e := by simpa [List.getElem?_append,pe] using hp
        have atQ : rest[q-out.events.length]? = some f := by simpa [List.getElem?_append,qe] using hq
        exact ih.ordered _ _ e f t pc qc (by omega) atP atQ he hf

/-- A single thread cannot issue the same instruction site twice. -/
theorem same_site_unique {s final : State n} {events : List (Event n)} (run : Runs cfg program s events final) (straight : Straight program)
    (p q : Nat) (e f : Event n) (t : Fin n) (pc : Nat)
    (hp : events[p]? = some e) (hq : events[q]? = some f)
    (he : stamp e = some (t,pc)) (hf : stamp f = some (t,pc)) : p=q := by
  have order := (runs_progress run straight).ordered
  rcases lt_trichotomy p q with before | same | after
  · have := order p q e f t pc pc before hp hq he hf; omega
  · exact same
  · have := order q p f e t pc pc after hq hp hf he; omega

/-- Instruction positions recover the actual order of a thread's events. -/
theorem position_iff_pc {s final : State n} {events : List (Event n)} (run : Runs cfg program s events final) (straight : Straight program)
    (p q : Nat) (e f : Event n) (t : Fin n) (pc qc : Nat)
    (hp : events[p]? = some e) (hq : events[q]? = some f)
    (he : stamp e = some (t,pc)) (hf : stamp f = some (t,qc)) : p<q ↔ pc<qc := by
  have order := (runs_progress run straight).ordered
  constructor
  · exact fun h => order p q e f t pc qc h hp hq he hf
  · intro h
    rcases lt_trichotomy p q with before | same | after
    · exact before
    · subst q
      have eq : e=f := Option.some.inj (hp.symm.trans hq)
      subst f
      have pair := Option.some.inj (he.symm.trans hf)
      have := congrArg Prod.snd pair
      omega
    · have := order q p f e t qc pc after hq hp hf he; omega

end Ptx.Scalar.Parallel.Control

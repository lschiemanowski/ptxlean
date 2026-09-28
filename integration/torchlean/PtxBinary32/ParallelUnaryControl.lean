import PtxBinary32.ParallelUnary

/-! Per-thread instruction order for the barrier-free adapter. This proof
measure restricts neither candidate loads nor arithmetic outcomes. -/
namespace Ptx.Scalar.ParallelUnary

def StraightInstr : Instr → Prop
  | .scalar i => ∀label, i.op≠.bra label
  | _ => True

def Straight (program : List Instr) : Prop := ∀i∈program, StraightInstr i

def cursor (s : State n) (thread : Fin n) : Nat :=
  2*(s.lanes thread).scalar.pc + if (s.lanes thread).halted then 1 else 0

theorem scalar_next_pc (h : Scalar.eval candidate i old=.next next event)
    (straight : ∀label, i.op≠.bra label) : next.pc=old.pc+1 := by
  cases i with
  | mk guard op =>
    cases op <;> cases hg : guard.eval old <;> simp only [Scalar.eval,hg,↓reduceIte] at h
    all_goals first
      | (obtain ⟨rfl,rfl⟩ := Scalar.StepResult.next.inj h; rfl)
      | contradiction
      | (exact False.elim (straight _ rfl))
      | (split at h <;> first | contradiction | (obtain ⟨rfl,rfl⟩ := Scalar.StepResult.next.inj h; rfl))

variable {n : Nat} {s t final : State n} {selected : Fin n} {event : Event n}

theorem exec_progress (exec : Exec candidate selected i s t event)
    (live : (s.lanes selected).halted=false) (straight : StraightInstr i) :
    cursor s selected=2*event.pc ∧ 2*event.pc<cursor t selected := by
  have origin := exec_origin exec
  have before : cursor s selected=2*event.pc := by rw [origin.2.1]; simp [cursor,live]
  refine ⟨before,?_⟩
  rw [origin.2.1]
  cases exec with
  | scalarNext h =>
    have pc := scalar_next_pc h straight
    simp [cursor,install,input,live,pc]
  | scalarHalted h =>
    rw [(Scalar.eval_halted h).1]
    simp [cursor,install,input]
  | binary h =>
    have pc := (Scalar.Binary32.eval_frame _ _ _ _ h).1
    simp [cursor,setLane,live,pc]
  | exponential h =>
    have pc := (Scalar.Exponential.eval_frame _ _ _ _ h).1
    simp [cursor,setLane,live,pc]
  | reciprocal h =>
    have pc := (Scalar.Reciprocal.eval_frame _ _ _ _ h).1
    simp [cursor,setLane,live,pc]

theorem step_progress (step : Step target program candidate selected s t event)
    (straight : Straight program) :
    (∀thread, cursor s thread≤cursor t thread) ∧
    cursor s event.thread=2*event.pc ∧ 2*event.pc<cursor t event.thread := by
  obtain ⟨_,live,i,fetch,exec⟩ := step
  have progress := exec_progress exec live (straight i (List.mem_of_getElem? fetch))
  have thread := (exec_origin exec).1
  refine ⟨?_,by simpa only [thread] using progress⟩
  intro other
  by_cases eq : other=selected
  · subst other; omega
  · have same := exec_other exec other eq
    simp only [cursor,same,le_refl]

structure TraceProgress (s : State n) (events : List (Event n)) (final : State n) : Prop where
  monotone : ∀thread, cursor s thread≤cursor final thread
  emitted : ∀(pos : Nat) (event : Event n), events[pos]?=some event →
    cursor s event.thread≤2*event.pc ∧ 2*event.pc<cursor final event.thread
  ordered : ∀(p q : Nat) (e f : Event n), p<q → events[p]?=some e → events[q]?=some f →
    e.thread=f.thread → e.pc<f.pc

theorem runs_progress (run : Runs target program s events final) (straight : Straight program) :
    TraceProgress s events final := by
  induction run with
  | nil => exact ⟨fun _ => le_rfl,by intros; simp_all,by intros; simp_all⟩
  | @cons candidate selected s middle event rest final step run ih =>
    have now := step_progress step straight
    refine ⟨fun thread => (now.1 thread).trans (ih.monotone thread),?_,?_⟩
    · intro pos e atPos
      cases pos with
      | zero =>
        have same : event=e := Option.some.inj atPos
        subst e
        exact ⟨now.2.1.le,now.2.2.trans_le (ih.monotone _)⟩
      | succ pos =>
        have bounds := ih.emitted pos e atPos
        exact ⟨(now.1 _).trans bounds.1,bounds.2⟩
    · intro p q e f before hp hq thread
      cases p with
      | zero =>
        have same : event=e := Option.some.inj hp
        subst e
        cases q with
        | zero => omega
        | succ q =>
          have later := (ih.emitted q f hq).1
          rw [← thread] at later
          have first := now.2.2
          omega
      | succ p =>
        cases q with
        | zero => omega
        | succ q => exact ih.ordered p q e f (by omega) hp hq thread

/-- Event positions and instruction sites have the same strict order in a lane. -/
theorem position_iff_pc (run : Runs target program s events final) (straight : Straight program)
    (p q : Nat) (e f : Event n) (hp : events[p]?=some e) (hq : events[q]?=some f)
    (thread : e.thread=f.thread) : p<q ↔ e.pc<f.pc := by
  have order := (runs_progress run straight).ordered
  constructor
  · exact fun before => order p q e f before hp hq thread
  · intro less
    rcases lt_trichotomy p q with before | same | after
    · exact before
    · subst q
      have same := Option.some.inj (hp.symm.trans hq)
      subst f
      omega
    · have reverse := order q p f e after hq hp thread.symm
      omega

theorem same_site_unique (run : Runs target program s events final) (straight : Straight program)
    (p q : Nat) (e f : Event n) (hp : events[p]?=some e) (hq : events[q]?=some f)
    (thread : e.thread=f.thread) (site : e.pc=f.pc) : p=q := by
  rcases lt_trichotomy p q with before | same | after
  · have := (position_iff_pc run straight p q e f hp hq thread).mp before; omega
  · exact same
  · have := (position_iff_pc run straight q p f e hq hp thread.symm).mp after; omega

theorem step_cursor_le (step : Step target program candidate selected s t event)
    (straight : Straight program) : cursor t selected≤cursor s selected+2 := by
  obtain ⟨_,live,i,fetch,exec⟩ := step
  have shape := straight i (List.mem_of_getElem? fetch)
  cases exec with
  | scalarNext h =>
    have pc := scalar_next_pc h shape
    simp [Nat.mul_add,cursor,install,input,live,pc]
  | scalarHalted h =>
    rw [(Scalar.eval_halted h).1]
    simp [cursor,install,input,live]
  | binary h => simp [Nat.mul_add,cursor,setLane,live,(Scalar.Binary32.eval_frame _ _ _ _ h).1]
  | exponential h => simp [Nat.mul_add,cursor,setLane,live,(Scalar.Exponential.eval_frame _ _ _ _ h).1]
  | reciprocal h => simp [Nat.mul_add,cursor,setLane,live,(Scalar.Reciprocal.eval_frame _ _ _ _ h).1]

/-- A completed lane cannot skip an instruction site. The cursor also covers
its terminating exit, which advances only the halted bit. -/
theorem runs_site (run : Runs target program s events final) (straight : Straight program)
    (thread : Fin n) (site : Nat) (start : cursor s thread≤2*site)
    (finish : 2*site<cursor final thread) :
    ∃event∈events, event.thread=thread ∧ event.pc=site := by
  induction run with
  | nil => omega
  | @cons candidate selected s middle event rest final step run ih =>
    by_cases later : cursor middle thread≤2*site
    · obtain ⟨e,mem,owner,pc⟩ := ih later finish
      exact ⟨e,List.mem_cons_of_mem _ mem,owner,pc⟩
    · have owner : selected=thread := by
        by_contra ne
        have same := step_other step thread (Ne.symm ne)
        simp only [cursor,same] at later
        exact later start
      subst selected
      have origin := step_origin step
      have progress := step_progress step straight
      have upper := step_cursor_le step straight
      have before : cursor s thread=2*event.pc := by simpa [origin.1] using progress.2.1
      exact ⟨event,by simp,origin.1,by omega⟩

end Ptx.Scalar.ParallelUnary

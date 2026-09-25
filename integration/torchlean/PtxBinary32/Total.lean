import PtxBinary32.Mixed

/-! A proof certificate for all dispatch choices, not a fuel-based execution
semantics. The count includes the actual terminal instruction. -/
namespace Ptx.Scalar.Mixed

/-- Every possible dispatch is successful, and every next state has one fewer
remaining instruction. Dispatch existence is supplied by the original semantics. -/
def Total (target : Ptx.Target) (program : List Instr) (post : State → Prop) : Nat → State → Prop
  | 0, _ => False
  | n+1, s => ∀ outcome, Dispatch target program s outcome → match outcome with
    | .next next _ => Total target program post n next
    | .halted final _ => n = 0 ∧ post final
    | .fault _ | .unsupported _ => False

theorem Total.mono (h : Total target program post n s)
    (implies : ∀ final, post final → post' final) : Total target program post' n s := by
  induction n generalizing s with
  | zero => exact h.elim
  | succ n ih =>
    intro outcome step
    have hs := h outcome step
    cases outcome with
    | next next event => exact ih hs
    | halted final event => exact ⟨hs.1, implies _ hs.2⟩
    | fault _ | unsupported _ => exact hs

theorem Total.scalar_next (fetch : program[s.pc]? = some (.scalar i))
    (evaluated : Scalar.eval none i s = .next next event)
    (tail : Total target program post n next) : Total target program post (n+1) s := by
  intro outcome step
  have eq := eval_scalar_iff.mp ((dispatch_fetch fetch).mp step).2
  simp only [evaluated, liftScalar] at eq
  subst outcome
  exact tail

theorem Total.scalar_halt (fetch : program[s.pc]? = some (.scalar i))
    (evaluated : Scalar.eval none i s = .halted final event) (hp : post final) :
    Total target program post 1 s := by
  intro outcome step
  have eq := eval_scalar_iff.mp ((dispatch_fetch fetch).mp step).2
  simp only [evaluated, liftScalar] at eq
  subst outcome
  exact ⟨rfl,hp⟩

theorem Total.binary32 (fetch : program[s.pc]? = some (.binary32 i))
    (enabled : i.guard.eval s = true)
    (tail : ∀ value, Ptx.Binary32.Results i.operation (i.left.eval s) (i.right.eval s) value →
      Total target program post n {s with pc := s.pc+1, regs := Scalar.update s.regs i.destination value}) :
    Total target program post (n+1) s := by
  intro outcome step
  obtain ⟨next,event,he,eq⟩ := eval_binary32_iff.mp ((dispatch_fetch fetch).mp step).2
  obtain ⟨value,hv,rfl,rfl⟩ := (Scalar.Binary32.eval_true_iff i s _ _ enabled).mp he
  subst outcome
  exact tail value hv

theorem Total.exists_run (h : Total target program post n s) (eligible : Eligible target) :
    ∃ final events, Run target program s final .halted events ∧ events.length = n ∧ post final := by
  induction n generalizing s with
  | zero => exact h.elim
  | succ n ih =>
    obtain ⟨outcome,step⟩ := dispatch_exists target program s eligible
    have hs := h outcome step
    cases outcome with
    | next next event =>
      obtain ⟨final,events,run,len,hp⟩ := ih hs
      exact ⟨final,event::events,.next step run,by simp [len],hp⟩
    | halted final event =>
      obtain ⟨rfl,hp⟩ := hs
      exact ⟨final,[event],.halted step,rfl,hp⟩
    | fault _ | unsupported _ => exact hs.elim

theorem Total.correct (h : Total target program post n s)
    (run : Run target program s final status events) :
    status = .halted ∧ events.length = n ∧ post final := by
  induction run generalizing n with
  | next step run ih =>
    cases n with
    | zero => exact h.elim
    | succ n =>
      obtain ⟨hs,hl,hp⟩ := ih (h _ step)
      exact ⟨hs,by simp [hl],hp⟩
  | halted step =>
    cases n with
    | zero => exact h.elim
    | succ n =>
      obtain ⟨rfl,hp⟩ := h _ step
      exact ⟨rfl,rfl,hp⟩
  | fault step | unsupported step =>
    cases n with
    | zero => exact h.elim
    | succ n => exact (h _ step).elim

theorem Total.prefix (h : Total target program post n s)
    (path : Path (Advances target program) s events middle) :
    events.length < n ∧ Total target program post (n-events.length) middle := by
  induction path generalizing n with
  | nil =>
    cases n with
    | zero => exact h.elim
    | succ n => exact ⟨by simp, by simpa using h⟩
  | cons step path ih =>
    cases n with
    | zero => exact h.elim
    | succ n =>
      obtain ⟨bound,tail⟩ := ih (h _ step)
      exact ⟨by simp only [List.length_cons]; omega, by simpa using tail⟩

theorem Total.no_infinite (h : Total target program post n s) :
    ¬ ∃ (states : Nat → State) (events : Nat → Event), states 0 = s ∧
      ∀ k, Advances target program (states k) (events k) (states (k+1)) := by
  rintro ⟨states,events,start,steps⟩
  have paths : ∀ k, Path (Advances target program) (states 0)
      (List.ofFn (fun i : Fin k => events i.val)) (states k) := by
    intro k
    induction k with
    | zero => exact .nil
    | succ k ih =>
      rw [List.ofFn_succ_last]
      exact ih.append (.cons (steps k) .nil)
  have bound := (h.prefix (start ▸ paths n)).1
  simp at bound

end Ptx.Scalar.Mixed

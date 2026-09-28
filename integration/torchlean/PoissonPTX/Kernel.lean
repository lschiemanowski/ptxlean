import PoissonPTX.Residual

namespace PtxTorchLean.Poisson.PTX.Kernel

/-- Launch-provided values. This does not assert a physical driver/ABI theorem. -/
structure Context where
  arena : Word
  lane : BitVec 32
  group : BitVec 32

inductive Instr where
  | parameter (dst : Nat)
  | lane (dst : Nat)
  | group (dst : Nat)
  | mad32 (dst a : Nat) (scale : BitVec 32) (b : Nat)
  | ge32 (a : Nat) (limit : BitVec 32)
  | predRet
  | data (op : Op)
  | ret
  deriving DecidableEq, Repr

structure State where
  core : PTX.State
  predicate : Bool
  halted : Bool

/-- Integer registers contain the zero-extended 32-bit word. -/
def u32 (w : Word) : BitVec 32 := w.setWidth 32

def scalar (s : State) (r : Nat) (w : Word) : State := {s with core := assign s.core r w}
def advance (s : State) : State := {s with core := PTX.advance s.core}
def halt (s : State) : State := {advance s with halted := true}

def simple (ctx : Context) (i : Instr) (s : State) : State :=
  match i with
  | .parameter dst => scalar s dst ctx.arena
  | .lane dst => scalar s dst (ctx.lane.setWidth 64)
  | .group dst => scalar s dst (ctx.group.setWidth 64)
  | .mad32 dst a scale b => scalar s dst ((u32 (s.core.regs a)*scale+u32 (s.core.regs b)).setWidth 64)
  | .ge32 a limit => {advance s with predicate := decide ((u32 (s.core.regs a)).toNat ≥ limit.toNat)}
  | .predRet => if s.predicate then halt s else advance s
  | .ret => halt s
  | .data _ => s -- not used by Eval; data is handled by PTX.Eval below

inductive Eval (ctx : Context) : Instr → State → State → Prop where
  | simple (ordinary : ∀ op, instruction ≠ .data op) : Eval ctx instruction s (simple ctx instruction s)
  | data (h : PTX.Eval op s.core t) : Eval ctx (.data op) s {s with core := t}

/-- Execution consumes fetched code, halting at an actual ret. There is no
successful case for an empty instruction list or an invalid load/store. -/
inductive Exec (ctx : Context) : List Instr → State → State → Prop where
  | next (running : s.halted = false) (step : Eval ctx i s middle)
      (continues : middle.halted = false) (rest : Exec ctx code middle t) : Exec ctx (i::code) s t
  | stop (running : s.halted = false) (step : Eval ctx i s t)
      (stopped : t.halted = true) : Exec ctx (i::code) s t

def Step (ctx : Context) (program : List Instr) (s t : State) : Prop :=
  s.halted = false ∧ ∃ i, program[s.core.pc]? = some i ∧ Eval ctx i s t

inductive Run (ctx : Context) (program : List Instr) : State → State → Prop where
  | stop : Step ctx program s t → t.halted = true → Run ctx program s t
  | next : Step ctx program s middle → middle.halted = false → Run ctx program middle t → Run ctx program s t

theorem simple_pc (ordinary : ∀ op, i ≠ Instr.data op) :
    (simple ctx i s).core.pc = s.core.pc+1 := by
  cases i <;> simp_all [simple,scalar,advance,halt,assign,PTX.advance]
  split <;> rfl

theorem eval_pc (h : Eval ctx i s t) : t.core.pc = s.core.pc+1 := by
  cases h with
  | simple hn => exact simple_pc hn
  | data h => exact PTX.eval_pc h

theorem exec_fetched (h : Exec ctx code s t) (precode : List Instr)
    (pc : s.core.pc = precode.length) : Run ctx (precode++code) s t := by
  induction h generalizing precode with
  | @stop i s t code running he stopped =>
    exact .stop ⟨running,i,by simp [pc],he⟩ stopped
  | @next i s middle code t running he continues rest ih =>
    apply Run.next ⟨running,i,by simp [pc],he⟩ continues
    have hm : middle.core.pc = (precode++[i]).length := by simp [eval_pc he,pc]
    simpa [List.append_assoc] using ih (precode++[i]) hm

/-- Every completed fetched run yields the corresponding instruction execution;
this excludes an unproved assumption about the instruction sequence followed. -/
theorem run_exec (h : Run ctx program s t) :
    ∀ precode code, program = precode++code → s.core.pc = precode.length → Exec ctx code s t := by
  induction h with
  | @stop s t step stopped =>
    intro precode code hp pc
    obtain ⟨running,i,fetch,he⟩ := step
    cases code with
    | nil => simp [hp,pc] at fetch
    | cons j rest =>
      have hi : j=i := by simpa [hp,pc] using fetch
      subst j
      exact .stop running he stopped
  | @next s middle t step continues rest ih =>
    intro precode code hp pc
    obtain ⟨running,i,fetch,he⟩ := step
    cases code with
    | nil => simp [hp,pc] at fetch
    | cons j tail =>
      have hi : j=i := by simpa [hp,pc] using fetch
      subst j
      apply Exec.next running he continues
      apply ih (precode++[i]) tail
      · simpa [List.append_assoc] using hp
      · simp [eval_pc he,pc]

theorem exec_ordinary_iff (ordinary : ∀ op, i ≠ Instr.data op) (running : s.halted = false) :
    Exec ctx (i::code) s t ↔
      (simple ctx i s = t ∧ t.halted = true) ∨
      ((simple ctx i s).halted = false ∧ Exec ctx code (simple ctx i s) t) := by
  constructor
  · intro h; cases h with
    | stop _ he hs => cases he with
      | simple _ => exact Or.inl ⟨rfl,hs⟩
      | data _ => simp_all
    | next _ he hc rest => cases he with
      | simple _ => exact Or.inr ⟨hc,rest⟩
      | data _ => simp_all
  · rintro (⟨rfl,hs⟩ | ⟨hc,rest⟩)
    · exact .stop running (.simple ordinary) hs
    · exact .next running (.simple ordinary) hc rest

theorem exec_nonhalting_iff (ordinary : ∀ op, i ≠ Instr.data op)
    (running : s.halted = false) (continues : (simple ctx i s).halted = false) :
    Exec ctx (i::code) s t ↔ Exec ctx code (simple ctx i s) t := by
  rw [exec_ordinary_iff ordinary running]
  have impossible : ¬ (simple ctx i s = t ∧ t.halted = true) := by
    rintro ⟨rfl,h⟩; simp [continues] at h
  simp [impossible,continues]

theorem exec_halting_iff (ordinary : ∀ op, i ≠ Instr.data op)
    (running : s.halted = false) (stopped : (simple ctx i s).halted = true) :
    Exec ctx (i::code) s t ↔ t = simple ctx i s := by
  rw [exec_ordinary_iff ordinary running]
  constructor
  · rintro (⟨he,_⟩ | ⟨hc,_⟩)
    · exact he.symm
    · simp [stopped] at hc
  · rintro rfl; exact Or.inl ⟨rfl,stopped⟩

/-- A branch-free data block preserves the predicate and the running flag. -/
theorem block_exec (h : PTX.Block body s.core t) (running : s.halted = false)
    (rest : Exec ctx suffix {s with core := t} final) :
    Exec ctx (body.map Instr.data ++ suffix) s final := by
  induction body generalizing s with
  | nil => cases h; exact rest
  | cons op ops ih =>
    cases h with
    | cons he hb =>
      exact .next running (.data he) running (ih hb running rest)

/-- Inversion recovers every actual data instruction from a complete run. -/
theorem exec_block (h : Exec ctx (body.map Instr.data ++ suffix) s final) :
    ∃ middle, PTX.Block body s.core middle ∧ Exec ctx suffix {s with core := middle} final := by
  induction body generalizing s with
  | nil => exact ⟨s.core,.nil,by simpa using h⟩
  | cons op ops ih =>
    cases h with
    | stop running he stopped => cases he with
      | simple ordinary => exact False.elim (ordinary op rfl)
      | data _ => simp_all
    | next running he continues rest => cases he with
      | simple ordinary => exact False.elim (ordinary op rfl)
      | data he =>
        obtain ⟨middle,hb,hr⟩ := ih rest
        exact ⟨middle,.cons he hb,hr⟩

/-- A checked interpreter for the selected instruction forms. Exhaustion or an
invalid fetch/access returns none; only an actual return gives a final state. -/
def step (ctx : Context) (program : List Instr) (s : State) : Option State := do
  if s.halted then none else do
    let i ← program[s.core.pc]?
    match i with
    | .data op => return {s with core := (← PTX.eval op s.core)}
    | i => return simple ctx i s

def execute (ctx : Context) (program : List Instr) : Nat → State → Option State
  | 0,_ => none
  | fuel+1,s => do
    let next ← step ctx program s
    if next.halted then some next else execute ctx program fuel next

theorem step_sound (h : step ctx program s = some t) : Step ctx program s t := by
  unfold step at h
  split at h
  · simp at h
  · rename_i running
    have hs : s.halted = false := Bool.eq_false_of_not_eq_true running
    cases hf : program[s.core.pc]? with
    | none => simp [hf] at h
    | some i =>
      refine ⟨hs,i,hf,?_⟩
      cases i with
      | data op =>
        simp only [hf] at h
        dsimp only [Bind.bind, Option.bind, Pure.pure] at h
        cases hd : PTX.eval op s.core with
        | none => simp [hd] at h
        | some next => simp [hd] at h; subst t; exact .data (PTX.eval_sound hd)
      | _ => simp [hf] at h; subst t; exact .simple (by simp)

theorem execute_sound (h : execute ctx program fuel s = some t) : Run ctx program s t := by
  induction fuel generalizing s with
  | zero => simp [execute] at h
  | succ fuel ih =>
    simp only [execute] at h
    cases hs : step ctx program s with
    | none => simp [hs] at h
    | some next =>
      simp only [hs] at h
      dsimp only [Bind.bind, Option.bind, Pure.pure] at h
      split at h
      · cases h; exact .stop (step_sound hs) (by assumption)
      · exact .next (step_sound hs) (Bool.eq_false_of_not_eq_true (by assumption)) (ih h)

end PtxTorchLean.Poisson.PTX.Kernel

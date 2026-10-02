import PoissonPTX.IndexedMemory

namespace PtxTorchLean.Poisson.PTX.Flow

/-- The unsigned comparisons used by the node assembly and reduction loops. -/
inductive Compare where
  | ge | ne | lt
  deriving DecidableEq, Repr

def Compare.apply (comparison : Compare) (a b : Word) : Bool :=
  match comparison with
  | .ge => decide ((Kernel.u32 a).toNat ≥ (Kernel.u32 b).toNat)
  | .ne => Kernel.u32 a != Kernel.u32 b
  | .lt => decide ((Kernel.u32 a).toNat < (Kernel.u32 b).toNat)

inductive Source where
  | arena | lane | group
  deriving DecidableEq, Repr

def source (ctx : Kernel.Context) : Source → Word
  | .arena => ctx.arena
  | .lane => ctx.lane.setWidth 64
  | .group => ctx.group.setWidth 64

inductive Instr where
  | data (op : Indexed.Instr)
  | context (dst : Nat) (src : Source)
  | compare (dst : Nat) (comparison : Compare) (a b : Operand)
  | branch (predicate : Nat) (when : Bool) (target : Nat)
  | jump (target : Nat)
  | select (predicate : Nat) (when : Bool) (dst : Nat) (value : Operand)
  | predRet (predicate : Nat) (when : Bool)
  | ret
  deriving DecidableEq, Repr

structure State where
  core : PTX.State
  predicates : Nat → Bool
  halted : Bool

def next (s : State) : State := {s with core:=advance s.core}
def halt (s : State) : State := {next s with halted:=true}
def goto (s : State) (target : Nat) : State := {s with core:={s.core with pc:=target}}

def simple (ctx : Kernel.Context) (i : Instr) (s : State) : State :=
  match i with
  | .data _ => s
  | .context dst src => {s with core:=assign s.core dst (source ctx src)}
  | .compare dst cmp a b => {next s with predicates:=Function.update s.predicates dst (cmp.apply (a.eval s.core) (b.eval s.core))}
  | .branch p b target => if s.predicates p=b then goto s target else next s
  | .jump target => goto s target
  | .select p b dst value => if s.predicates p=b then {s with core:=assign s.core dst (value.eval s.core)} else next s
  | .predRet p b => if s.predicates p=b then halt s else next s
  | .ret => halt s

/-- Data access is the existing checked byte-memory semantics. Control steps
inspect actual registers and predicates; no branch outcome is supplied. -/
inductive Eval (ctx : Kernel.Context) : Instr → State → State → Prop where
  | data (step : Indexed.Eval op s.core t) : Eval ctx (.data op) s {s with core:=t}
  | simple (ordinary : ∀ op, i≠.data op) : Eval ctx i s (simple ctx i s)

def Step (ctx : Kernel.Context) (program : List Instr) (s t : State) : Prop :=
  s.halted=false ∧ ∃ i, program[s.core.pc]?=some i ∧ Eval ctx i s t

inductive Runs (ctx : Kernel.Context) (program : List Instr) : State → State → Prop where
  | nil : Runs ctx program s s
  | cons : Step ctx program s t → Runs ctx program t u → Runs ctx program s u

def eval (ctx : Kernel.Context) (i : Instr) (s : State) : Option State :=
  match i with
  | .data op => (Indexed.eval op s.core).map fun t => {s with core:=t}
  | _ => some (simple ctx i s)

def tick (ctx : Kernel.Context) (program : List Instr) (s : State) : Option State :=
  if s.halted then none else program[s.core.pc]? >>= fun i => eval ctx i s

/-- Fuel bounds a witness search, not the relational execution or correctness
statement. Running out of fuel cannot produce a successful returned state. -/
def execute (ctx : Kernel.Context) (program : List Instr) : Nat → State → Option State
  | 0,s => if s.halted then some s else none
  | fuel+1,s => if s.halted then some s else tick ctx program s >>= execute ctx program fuel

theorem eval_sound (h : eval ctx i s=some t) : Eval ctx i s t := by
  cases i with
  | data op =>
    simp only [eval,Option.map_eq_some_iff] at h
    obtain ⟨u,step,rfl⟩ := h
    exact .data (Indexed.eval_sound step)
  | _ => cases h; apply Eval.simple; intro op h; cases h

theorem tick_sound (h : tick ctx program s=some t) : Step ctx program s t := by
  unfold tick at h
  split at h
  · simp at h
  · rename_i running
    change (program[s.core.pc]?.bind fun i => eval ctx i s)=some t at h
    simp only [Option.bind_eq_some_iff] at h
    obtain ⟨i,fetch,step⟩ := h
    exact ⟨by cases h : s.halted <;> simp_all, i,fetch,eval_sound step⟩

theorem execute_sound (h : execute ctx program fuel s=some t) : Runs ctx program s t ∧ t.halted=true := by
  induction fuel generalizing s with
  | zero =>
    simp only [execute] at h
    split at h
    · cases h; exact ⟨.nil,by assumption⟩
    · simp at h
  | succ fuel ih =>
    simp only [execute] at h
    split at h
    · cases h; exact ⟨.nil,by assumption⟩
    · change ((tick ctx program s).bind (execute ctx program fuel))=some t at h
      simp only [Option.bind_eq_some_iff] at h
      obtain ⟨mid,step,rest⟩ := h
      obtain ⟨run,done⟩ := ih rest
      exact ⟨.cons (tick_sound step) run,done⟩

theorem append (first : Runs ctx program s t) (second : Runs ctx program t u) : Runs ctx program s u := by
  induction first with
  | nil => exact second
  | cons step rest ih => exact .cons step (ih second)

theorem halted_no_step (h : s.halted=true) : ¬Step ctx program s t := by
  intro step; have no := step.1; rw [h] at no; cases no

theorem invariant {P : State → Prop} (run : Runs ctx program s t) (initial : P s)
    (preserves : ∀ s t, Step ctx program s t → P s → P t) : P t := by
  induction run with
  | nil => exact initial
  | cons step rest ih => exact ih (preserves _ _ step initial)

end PtxTorchLean.Poisson.PTX.Flow

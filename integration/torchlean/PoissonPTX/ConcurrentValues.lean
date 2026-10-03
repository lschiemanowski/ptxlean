import PoissonPTX.ConcurrentAddress

/-! A conservative register-value analysis. Loads obtain an optional numerical
contract; arithmetic combines known operands. Unknown assignments erase facts.
The soundness theorem requires evidence from actual load events. -/
namespace PtxTorchLean.Poisson.PTX.Concurrent.Values

abbrev Table (n : Nat) := Nat → Option (Fin n → Float)
def empty : Table n := fun _ => none

def operand (table : Table n) : Operand → Option (Fin n → Float)
  | .reg r => table r
  | .imm w => some (fun _ => decode w)
  | .offset .. => none

def transfer (loads : Nat → Option (Fin n → Float)) (pc : Nat) (table : Table n) : Instr → Table n
  | .data (.load64 _ dst _) => Function.update table dst (loads pc)
  | .data (.fp op dst a b) => Function.update table dst
      ((operand table a).bind fun x => (operand table b).map fun y t => op.apply (x t) (y t))
  | .data (.mov dst _) | .data (.mul32 dst _ _) | .data (.add32 dst _ _) |
    .data (.add64 dst _ _) | .data (.wide8 dst _) => Function.update table dst none
  | _ => empty

def Ready (table : Table n) (thread : Fin n) (s : PTX.State) : Prop :=
  ∀ r f, table r=some f → decode (s.regs r)=f thread

theorem empty_ready : Ready empty thread s := by intro r f h; cases h

theorem operand_ready (ready : Ready table thread s) (known : operand table arg=some f) :
    decode (arg.eval s)=f thread := by
  cases arg with
  | reg r => exact ready r f known
  | imm w => cases known; rfl
  | offset => cases known

theorem assign_ready (ready : Ready table thread s)
    (value : ∀ f, known=some f → decode word=f thread) :
    Ready (Function.update table dst known) thread (assign s dst word) := by
  intro r f atR
  by_cases eq : r=dst
  · subst r; simp only [Function.update_self] at atR
    simpa only [assign,advance,Function.update_self] using value f atR
  · simp only [Function.update_of_ne eq] at atR
    simpa only [assign,advance,Function.update_of_ne eq] using ready r f atR

theorem data_ready (h : Data op s t effect) (ready : Ready table thread s)
    (reads : ∀ a, effect=some a → a.data.store=false → ∀ f, loads s.pc=some f →
      decode a.data.value=f thread) : Ready (transfer loads s.pc table (.data op)) thread t := by
  cases h with
  | ordinary plain he =>
    cases he <;> simp only [transfer] <;> try { exact assign_ready ready (by intro f h; cases h) }
    case fp op dst a b s out result =>
      apply assign_ready ready
      intro f known
      simp only [Option.bind_eq_some_iff,Option.map_eq_some_iff] at known
      obtain ⟨x,hx,y,hy,rfl⟩ := known
      simpa only [FP.Result,operand_ready ready hx,operand_ready ready hy] using result
    all_goals simp [ordinary] at plain
  | load => exact assign_ready ready (fun f hf => reads _ rfl rfl f hf)
  | store => exact empty_ready

def tag (program : List Instr) (initial : Table n) (loads : Nat → Option (Fin n → Float)) : Nat → Table n
  | 0 => initial
  | pc+1 => match program[pc]? with
    | some i => transfer loads pc (tag program initial loads pc) i
    | none => empty

def Entries (program : List Instr) (initial : Table n) (loads : Nat → Option (Fin n → Float)) : Prop :=
  ∀ (pc active target : Nat), program[pc]?=some (.skip active target) →
    ∀ thread s, Ready (tag program initial loads target) thread s

def Reads (loads : Nat → Option (Fin n → Float)) (events : List (Event n)) : Prop :=
  ∀ thread a, Event.data thread a∈events → a.data.store=false →
    ∀ f, loads a.data.pc=some f → decode a.data.value=f thread

def Invariant (program : List Instr) (initial : Table n) (loads : Nat → Option (Fin n → Float))
    (s : State n) : Prop := ∀ t, Ready (tag program initial loads (s.lanes t).pc) t (s.lanes t)

theorem step_invariant (step : Step cfg program selected s out) (aligned : Aligned s)
    (inv : Invariant program initial loads s) (entries : Entries program initial loads)
    (reads : Reads loads out.events) : Invariant program initial loads out.state := by
  obtain ⟨fresh,i,fetch,h⟩ := step
  cases h with
  | data hd =>
    intro thread
    by_cases eq : thread=selected
    · subst thread
      simp only [setLane,Function.update_self]
      rw [data_pc hd]
      simp only [tag,fetch]
      apply data_ready hd (inv selected)
      intro a ha read f hf
      have pc := access_pc (ha ▸ hd)
      exact reads selected a (by simp [ha]) read f (by simpa only [pc] using hf)
    · simpa [setLane,Function.update,eq] using inv thread
  | skip =>
    intro thread
    by_cases eq : thread=selected
    · subst thread
      simp only [setLane,Function.update_self]
      split
      · simp only [tag,fetch,transfer]; exact empty_ready
      · exact entries _ _ _ fetch _ _
    · simpa [setLane,Function.update,eq] using inv thread
  | @sync resource =>
    intro thread
    simp only [synchronize]
    split
    · exact inv thread
    · exact inv thread
    · rename_i released
      have same := release_aligned cfg s selected resource aligned released thread
      change Ready (tag program initial loads ((s.lanes thread).pc+1)) thread (advance (s.lanes thread))
      rw [same]; simp only [tag,fetch,transfer]; exact empty_ready

theorem runs_invariant (run : Runs cfg program start events final) (aligned : Aligned start)
    (inv : Invariant program initial loads start) (entries : Entries program initial loads)
    (reads : Reads loads events) : Invariant program initial loads final := by
  induction run with
  | nil => exact inv
  | cons step tail ih =>
    exact ih (step_aligned step aligned) (step_invariant step aligned inv entries
      (fun t a h => reads t a (List.mem_append_left _ h)))
      (fun t a h => reads t a (List.mem_append_right _ h))

end PtxTorchLean.Poisson.PTX.Concurrent.Values

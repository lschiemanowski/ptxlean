import PoissonPTX.Symbolic

namespace PtxTorchLean.Poisson.PTX.Concurrent.Symbolic
open Ptx

inductive Mode where
  | addresses | values
  deriving DecidableEq, Repr

/-- Address proofs discard all loaded and floating-point values. They therefore
need no read-value premise and cannot depend circularly on numerical correctness. -/
def update (mode : Mode) (regs : Registers) (op : Op) : Registers :=
  match mode,op with
  | .addresses,.load64 _ dst _ | .addresses,.fp _ dst _ _ => Function.update regs dst .unknown
  | _,op => data regs op

def transfer (mode : Mode) (regs : Registers) : Instr → Registers
  | .data op => update mode regs op
  | _ => regs

def atPC (mode : Mode) (code : List Instr) (seed : Registers) (pc : Nat) : Registers :=
  (code.take pc).foldl (transfer mode) seed

theorem at_zero : atPC mode code seed 0=seed := rfl

theorem at_next (fetch : code[pc]?=some i) :
    atPC mode code seed (pc+1)=transfer mode (atPC mode code seed pc) i := by
  unfold atPC
  rw [List.take_add_one]
  simp [fetch,List.foldl_append]

theorem update_sound (execution : Data op s t access) (hregs : Matches bases memory regs s)
    (reads : mode=.values → ∀ a, access=some a → a.data.store=false → a.data.value=memory a.space a.data.address) :
    Matches bases memory (update mode regs op) t := by
  cases mode with
  | values => exact data_sound execution hregs (reads rfl)
  | addresses =>
    cases op with
    | store64 sp addr src =>
      cases execution with
      | ordinary plain _ => simp [ordinary] at plain
      | store => cases sp <;> exact hregs
    | load64 sp dst addr =>
      cases execution with
      | ordinary plain _ => simp [ordinary] at plain
      | load => exact assign_sound hregs trivial
    | fp op dst a b =>
      cases execution with
      | ordinary plain he => cases he; exact assign_sound hregs trivial
    | _ => exact data_sound execution hregs (by intro a he; cases execution; simp at he)

/-- Active threads follow the linear instruction order; other threads can skip
bodies but cannot access data, as proved separately by the padding invariant. -/
def Guards (code : List Instr) (active : Nat) : Prop :=
  ∀ (pc : Nat) count target, code[pc]?=some (.skip count target) → count=active

def Invariant (mode : Mode) (code : List Instr) (active : Nat)
    (seeds : Fin n → Registers) (bases : Space → Word) (memory : Space → Nat → Word) (s : State n) : Prop :=
  ∀ thread, thread.val<active → Matches bases memory (atPC mode code (seeds thread) (s.lanes thread).pc) (s.lanes thread)

def Reads (memory : Space → Nat → Word) (events : List (Event n)) : Prop :=
  ∀ thread a, Event.data thread a∈events → a.data.store=false → a.data.value=memory a.space a.data.address

theorem step_invariant (step : Step cfg code selected s out) (aligned : Aligned s)
    (inv : Invariant mode code active seeds bases memory s) (guards : Guards code active)
    (reads : mode=.values → Reads memory out.events) :
    Invariant mode code active seeds bases memory out.state := by
  obtain ⟨fresh,i,fetch,dispatch⟩ := step
  cases dispatch with
  | data hd =>
    intro thread live
    by_cases eq : thread=selected
    · subst thread
      simp only [setLane,Function.update_self]
      rw [data_pc hd,at_next fetch]
      apply update_sound hd (inv selected live)
      intro modeEq a ha read
      apply reads modeEq selected a _ read
      simp [ha]
    · simpa [setLane,Function.update,eq] using inv thread live
  | skip =>
    intro thread live
    by_cases eq : thread=selected
    · subst thread
      have count := guards _ _ _ fetch
      simp only [setLane,Function.update_self]
      simp only [count,live,ite_true]
      rw [at_next fetch]
      exact inv selected live
    · simpa [setLane,Function.update,eq] using inv thread live
  | @sync resource =>
    intro thread live
    simp only [synchronize]
    split
    · exact inv thread live
    · exact inv thread live
    · rename_i released
      have same := release_aligned cfg s selected resource aligned released thread
      change Matches bases memory (atPC mode code (seeds thread) ((s.lanes thread).pc+1)) (advance (s.lanes thread))
      rw [same,at_next fetch]
      simpa [transfer,← same,Matches,advance] using inv thread live

theorem runs_invariant (run : Runs cfg code start events final) (aligned : Aligned start)
    (inv : Invariant mode code active seeds bases memory start) (guards : Guards code active)
    (reads : mode=.values → Reads memory events) :
    Invariant mode code active seeds bases memory final := by
  induction run with
  | nil => exact inv
  | cons step tail ih =>
    apply ih (step_aligned step aligned)
      (step_invariant step aligned inv guards (fun eq t a ha => reads eq t a (List.mem_append_left _ ha)))
    intro eq t a ha
    exact reads eq t a (List.mem_append_right _ ha)

/-- Symbolic operands at actual accesses, with their real emitting state. -/
theorem access_registers {start : State n} (run : Runs cfg code start events final) (aligned : Aligned start)
    (inv : Invariant mode code active seeds bases memory start) (guards : Guards code active)
    (reads : mode=.values → Reads memory events)
    (member : Event.data thread access∈events) (live : thread.val<active) :
    ∃ (before : State n) (op : Op) (next : PTX.State),
      code[(before.lanes thread).pc]?=some (.data op) ∧
      Data op (before.lanes thread) next (some access) ∧
      Matches bases memory (atPC mode code (seeds thread) access.data.pc) (before.lanes thread) := by
  obtain ⟨before,earlier,selected,out,suffix,hp,hs,hm,ht,he⟩ := run_access_prefix run member
  obtain ⟨eq,op,next,fetch,hd⟩ := step_access_origin hs hm
  subst selected
  have state := runs_invariant hp aligned inv guards (by
    intro modeEq t a ha
    apply reads modeEq t a _
    rw [he]; exact List.mem_append_left _ (List.mem_append_left _ ha)) thread live
  rw [← access_pc hd] at state
  exact ⟨before,op,next,fetch,hd,state⟩

end PtxTorchLean.Poisson.PTX.Concurrent.Symbolic

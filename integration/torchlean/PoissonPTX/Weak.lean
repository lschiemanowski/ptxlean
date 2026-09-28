import PoissonPTX.Kernel
import PoissonPTX.Sources

/-! Candidate instruction executions: global loads choose arbitrary words;
source constraints are checked separately. Stores record their actual address
and operand. Shared operations are outside this barrier-free interpreter. -/
namespace PtxTorchLean.Poisson.PTX.Weak
open Kernel Sources

/-- A choice is an unconstrained word, not a value oracle asserting correctness.
For arithmetic it must satisfy the same primitive result relation as PTX.Eval. -/
def data (choice : Word) (op : Op) (s : PTX.State) : Option PTX.State :=
  match op with
  | .load64 .global dst address =>
    if Valid64 s.globalStart s.globalBytes (address.eval s).toNat then
      some (assign s dst choice) else none
  | .fp fp dst a b =>
    if fp.Result (a.eval s) (b.eval s) choice then some (assign s dst choice) else none
  | .load64 .shared .. | .store64 .shared .. => none
  | op => PTX.eval op s

def access (op : Op) (s t : PTX.State) : List Access :=
  match op with
  | .load64 .global dst a => [⟨s.pc,false,(a.eval s).toNat,t.regs dst⟩]
  | .store64 .global a v => [⟨s.pc,true,(a.eval s).toNat,v.eval s⟩]
  | _ => []

def instruction (ctx : Context) (choice : Word) (i : Instr) (s : Kernel.State) :
    Option (Kernel.State × List Access) :=
  match i with
  | .data op => do
    let t ← data choice op s.core
    return ({s with core:=t},access op s.core t)
  | i => some (Kernel.simple ctx i s,[])

def step (ctx : Context) (program : List Instr) (choose : Nat → Word) (s : Kernel.State) :
    Option (Kernel.State × List Access) := do
  if s.halted then none else do
    let i ← program[s.core.pc]?
    instruction ctx (choose s.core.pc) i s

/-- Fuel is only an evaluation bound. Success requires fetching an actual return;
exhaustion, invalid fetch, invalid arithmetic and invalid addresses fail. -/
def execute (ctx : Context) (program : List Instr) (choose : Nat → Word) :
    Nat → Kernel.State → Option (Kernel.State × List Access)
  | 0,_ => none
  | fuel+1,s => do
    let (next,events) ← step ctx program choose s
    if next.halted then some (next,events) else do
      let (last,rest) ← execute ctx program choose fuel next
      return (last,events++rest)

/-- Labels come from the instruction that was fetched, not a separately supplied
address or footprint. -/
theorem access_origin (h : event ∈ access op s t) :
    (∃ dst a, op = .load64 .global dst a ∧ event = ⟨s.pc,false,(a.eval s).toNat,t.regs dst⟩) ∨
    (∃ a v, op = .store64 .global a v ∧ event = ⟨s.pc,true,(a.eval s).toNat,v.eval s⟩) := by
  cases op <;> simp_all [access]
  all_goals cases ‹Space› <;> simp_all [access]

theorem data_pc (h : data choice op s = some t) : t.pc=s.pc+1 := by
  cases op with
  | load64 sp dst a =>
    cases sp with
    | shared => simp [data] at h
    | global =>
      simp only [data] at h
      split at h
      · cases h; rfl
      · contradiction
  | store64 sp a v =>
    cases sp with
    | shared => simp [data] at h
    | global => exact PTX.eval_pc (PTX.eval_sound (op := .store64 .global a v) (by simpa [data] using h))
  | fp op dst a b =>
    simp only [data] at h
    split at h
    · cases h; rfl
    · contradiction
  | mov dst src => cases h; rfl
  | mul32 dst a b => cases h; rfl
  | add32 dst a b => cases h; rfl
  | add64 dst a b => cases h; rfl
  | wide8 dst index => cases h; rfl

end PtxTorchLean.Poisson.PTX.Weak

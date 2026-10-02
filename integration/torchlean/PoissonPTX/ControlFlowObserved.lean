import PoissonPTX.ControlFlow
import PoissonPTX.IndexedCandidate

namespace PtxTorchLean.Poisson.PTX.Flow.Observed

/-- Fetched control flow with explicit records for arbitrary candidate load
bits. Source admission is separate, including four-byte index observations. -/
inductive Eval (ctx : Kernel.Context) : Instr → State → State →
    Option Concurrent.Access → Option IndexSources.Access → Prop where
  | data (step : Indexed.Candidate.Data op s.core t access index) :
      Eval ctx (.data op) s {s with core:=t} access index
  | simple (ordinary : ∀ op, i≠.data op) : Eval ctx i s (simple ctx i s) none none

def Step (ctx : Kernel.Context) (program : List Instr) (s t : State)
    (access : Option Concurrent.Access) (index : Option IndexSources.Access) : Prop :=
  s.halted=false ∧ ∃ i, program[s.core.pc]?=some i ∧ Eval ctx i s t access index

inductive Runs (ctx : Kernel.Context) (program : List Instr) : State →
    List Concurrent.Access → List IndexSources.Access → State → Prop where
  | nil : Runs ctx program s [] [] s
  | cons : Step ctx program s t access index → Runs ctx program t words indices u →
      Runs ctx program s (access.toList++words) (index.toList++indices) u

/-- Once a candidate step's read bits are justified against its actual local
memory, it is a step of the existing relational instruction semantics. -/
theorem replay_step (step : Step ctx program s t access index)
    (words : ∀ a, access=some a → a.data.store=false →
      a.data.value=read64 (s.core.memory a.space) a.data.address)
    (indices : ∀ a, index=some a → a.value=read32 s.core.global a.address) :
    Flow.Step ctx program s t := by
  obtain ⟨running,i,fetch,execution⟩ := step
  refine ⟨running,i,fetch,?_⟩
  cases execution with
  | data one => exact .data (Indexed.Candidate.replay one words indices)
  | simple ordinary => exact .simple ordinary

theorem append (first : Runs ctx program s wa ia t) (second : Runs ctx program t wb ib u) :
    Runs ctx program s (wa++wb) (ia++ib) u := by
  induction first with
  | nil => exact second
  | cons step rest ih => simpa only [List.append_assoc] using Runs.cons step (ih second)

/-- Every recorded store comes from the corresponding fetched store opcode;
its address and bits are the operands of that actual pre-instruction state. -/
theorem store_shape (execution : Eval ctx op s t (some a) index) (store : a.data.store=true) :
    ∃ sp addr src, op=.data (.data (.store64 sp addr src)) ∧
      a=⟨sp,⟨s.core.pc,true,(addr.eval s.core).toNat,src.eval s.core⟩⟩ := by
  cases execution with
  | data one =>
    cases one with
    | data one =>
      cases one with
      | load => simp at store
      | store => exact ⟨_,_,_,rfl,rfl⟩

end PtxTorchLean.Poisson.PTX.Flow.Observed

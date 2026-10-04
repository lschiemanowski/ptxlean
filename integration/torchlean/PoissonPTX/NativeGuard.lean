import PoissonPTX.ConcurrentAddress
import PoissonPTX.ControlFlow

/-! Separately scheduled comparison and predicated branch. The counter is
factored into an original instruction slot and a within-slot phase. Memory and
barrier events retain slot labels; these are instruction identities, not PTX
byte addresses. The expansion and its physical instruction indices are separate.
No branch outcome or arithmetic result is supplied by a correctness premise. -/
namespace PtxTorchLean.Poisson.PTX.Concurrent.NativeGuard

structure State (n : Nat) where
  core : Concurrent.State n
  pending : Fin n → Bool
  predicate : Fin n → Bool

def start (s : Concurrent.State n) (flags : Fin n → Bool) : State n :=
  ⟨s,fun _ => false,flags⟩

def compared (s : State n) (thread : Fin n) (count : Nat) : State n :=
  {s with
    pending:=Function.update s.pending thread true,
    predicate:=Function.update s.predicate thread
      (Flow.Compare.ge.apply ((s.core.lanes thread).regs 14) (BitVec.ofNat 64 count))}

def branched (s : State n) (thread : Fin n) (target : Nat) : State n :=
  {s with
    core:=setLane s.core thread {s.core.lanes thread with
      pc:=if s.predicate thread then target else (s.core.lanes thread).pc+1},
    pending:=Function.update s.pending thread false}

/-- A true phase bit means the next fetched instruction is the branch, not
the comparison. Other lanes may execute between these two steps. -/
inductive Step (cfg : Config n) (program : List Instr) (thread : Fin n) :
    State n → List (Event n) → State n → Prop where
  | compare (fresh : s.core.barrier.arrived thread=false) (phase : s.pending thread=false)
      (fetch : program[(s.core.lanes thread).pc]?=some (.skip count target)) :
      Step cfg program thread s [] (compared s thread count)
  | branch (fresh : s.core.barrier.arrived thread=false) (phase : s.pending thread=true)
      (fetch : program[(s.core.lanes thread).pc]?=some (.skip count target)) :
      Step cfg program thread s [] (branched s thread target)
  | data (fresh : s.core.barrier.arrived thread=false) (phase : s.pending thread=false)
      (fetch : program[(s.core.lanes thread).pc]?=some (.data op))
      (actual : Data op (s.core.lanes thread) next access) :
      Step cfg program thread s (access.toList.map (Event.data thread))
        {s with core:=setLane s.core thread next}
  | sync (fresh : s.core.barrier.arrived thread=false) (phase : s.pending thread=false)
      (fetch : program[(s.core.lanes thread).pc]?=some (.sync resource)) :
      Step cfg program thread s (synchronize cfg s.core thread resource).events
        {s with core:=(synchronize cfg s.core thread resource).state}

inductive Runs (cfg : Config n) (program : List Instr) :
    State n → List (Event n) → State n → Prop where
  | nil : Runs cfg program s [] s
  | cons : Step cfg program thread s first middle → Runs cfg program middle rest final →
      Runs cfg program s (first++rest) final

/-- Pending comparisons retain their actual fetched count and computed flag.
Waiting lanes cannot also be halfway through a guard. -/
def Ready (program : List Instr) (s : State n) : Prop :=
  (∀ t, s.pending t=true → s.core.barrier.arrived t=false ∧
    ∃ count target, program[(s.core.lanes t).pc]?=some (.skip count target) ∧
      s.predicate t=decide (count≤t.val)) ∧
  (∀ t, ((s.core.lanes t).regs 14).toNat=t.val)

def CountsFit (program : List Instr) : Prop :=
  ∀ (pc count target : Nat), program[pc]?=some (.skip count target) → count<2^32

theorem initial {n : Nat} {s : Concurrent.State n} {flags : Fin n → Bool} (lanes : ∀ t, ((s.lanes t).regs 14).toNat=t.val) :
    Ready program (start s flags) := ⟨by simp [start],lanes⟩

theorem compare_value (lane : word.toNat=thread.val) (small : n≤2^32)
    (countFits : count<2^32) :
    Flow.Compare.ge.apply word (BitVec.ofNat 64 count)=decide (count≤(thread : Fin n).val) := by
  have low : thread.val<4294967296 := lt_of_lt_of_le thread.isLt small
  have countLow : count<4294967296 := countFits
  simp [Flow.Compare.apply,Kernel.u32,BitVec.toNat_setWidth,BitVec.toNat_ofNat,
    lane,Nat.mod_eq_of_lt low,Nat.mod_eq_of_lt countLow]

theorem branch_core (ready : Ready program s)
    (phase : s.pending thread=true)
    (fetch : program[(s.core.lanes thread).pc]?=some (.skip count target)) :
    (branched s thread target).core=setLane s.core thread
      {s.core.lanes thread with pc:=if thread.val<count then (s.core.lanes thread).pc+1 else target} := by
  obtain ⟨_,c,t,found,flag⟩ := ready.1 thread phase
  have eq := Option.some.inj (found.symm.trans fetch)
  cases eq
  simp only [branched,flag,decide_eq_true_eq]
  by_cases h : count≤thread.val <;> simp [h,show (thread.val<count) ↔ ¬ count≤thread.val by omega]

/-- Erasing one native comparison stutters; every other native instruction is
one actual step of the existing concurrent machine with identical events. -/
theorem project_step (actual : Step cfg program thread s events t) (ready : Ready program s) :
    Concurrent.Runs cfg program s.core events t.core := by
  cases actual with
  | compare => exact .nil
  | branch fresh phase fetch =>
    rw [branch_core ready phase fetch]
    exact .cons ⟨fresh,_,fetch,Dispatch.skip⟩ .nil
  | data fresh phase fetch hd =>
    simpa using Concurrent.Runs.cons ⟨fresh,_,fetch,Dispatch.data hd⟩ Concurrent.Runs.nil
  | sync fresh phase fetch =>
    simpa using Concurrent.Runs.cons ⟨fresh,_,fetch,Dispatch.sync⟩ Concurrent.Runs.nil

end PtxTorchLean.Poisson.PTX.Concurrent.NativeGuard

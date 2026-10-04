import PoissonPTX.NativeGuard
import PoissonPTX.ReductionOwnership

/-! The emitted tree has 76 instructions: the old 68 slots plus the second
instruction of each of eight guards. Targets below are real instruction indices
within the tree. Logical slot labels remain useful event identities. -/
namespace PtxTorchLean.Poisson.PTX.Concurrent.Reduction.Native
open Control

inductive Instr where
  | data (op : Op)
  | compare (count : Nat)
  | branch (target : Nat)
  | sync (resource : Fin 16)
  deriving DecidableEq, Repr

def position (slot : Nat) : Nat := slot+min 8 ((slot+3)/8)

def expand : Concurrent.Instr → List Instr
  | .data op => [.data op]
  | .skip count target => [.compare count,.branch (position target)]
  | .sync resource => [.sync resource]

def code : List Instr := program.flatMap expand

def pc (s : NativeGuard.State n) (thread : Fin n) : Nat :=
  position (s.core.lanes thread).pc + if s.pending thread then 1 else 0

theorem length : code.length=76 := by decide +kernel

theorem positions : ∀ slot : Fin 68,
    (match program[slot.val]? with
    | some (.data op) => decide (code[position slot.val]?=some (.data op) ∧
        position (slot.val+1)=position slot.val+1)
    | some (.skip count target) => decide (code[position slot.val]?=some (.compare count) ∧
        code[position slot.val+1]?=some (.branch (position target)) ∧
        position (slot.val+1)=position slot.val+2 ∧ target≤68 ∧ count<2^32)
    | some (.sync resource) => decide (code[position slot.val]?=some (.sync resource) ∧
        position (slot.val+1)=position slot.val+1)
    | none => false)=true := by decide +kernel

theorem located {slot : Nat} {i : Concurrent.Instr} (fetch : Control.program[slot]?=some i) :
    match i with
    | .data op => code[position slot]?=some (.data op) ∧ position (slot+1)=position slot+1
    | .skip count target => code[position slot]?=some (.compare count) ∧
        code[position slot+1]?=some (.branch (position target)) ∧
        position (slot+1)=position slot+2 ∧ target≤68 ∧ count<2^32
    | .sync resource => code[position slot]?=some (.sync resource) ∧ position (slot+1)=position slot+1 := by
  have bound := (List.getElem?_eq_some_iff.mp fetch).1
  rw [Control.length] at bound
  have h := positions ⟨slot,bound⟩
  cases i <;> simpa only [fetch,decide_eq_true_eq] using h

theorem counts : NativeGuard.CountsFit program := by
  intro slot count target fetch
  exact (located fetch).2.2.2.2

theorem compare_fetch {s : NativeGuard.State 256} (phase : s.pending thread=false)
    (fetch : program[(s.core.lanes thread).pc]?=some (.skip count target)) :
    code[pc s thread]?=some (.compare count) ∧
    pc (NativeGuard.compared s thread count) thread=pc s thread+1 := by
  simpa [pc,phase,NativeGuard.compared] using
    And.intro (located fetch).1 (Eq.refl (position (s.core.lanes thread).pc+1))

theorem branch_fetch {s : NativeGuard.State 256} (phase : s.pending thread=true)
    (fetch : program[(s.core.lanes thread).pc]?=some (.skip count target)) :
    code[pc s thread]?=some (.branch (position target)) ∧
    pc (NativeGuard.branched s thread target) thread=
      if s.predicate thread then position target else pc s thread+1 := by
  refine ⟨by simpa [pc,phase] using (located fetch).2.1,?_⟩
  cases flag : s.predicate thread <;>
    simp [pc,NativeGuard.branched,setLane,flag,phase,(located fetch).2.2.1,Nat.add_assoc]

theorem data_fetch {s : NativeGuard.State 256} (phase : s.pending thread=false)
    (fetch : program[(s.core.lanes thread).pc]?=some (.data op))
    (actual : Data op (s.core.lanes thread) next access) :
    code[pc s thread]?=some (.data op) ∧
    pc {s with core:=setLane s.core thread next} thread=pc s thread+1 := by
  refine ⟨by simpa [pc,phase] using (located fetch).1,?_⟩
  simp [pc,setLane,phase,data_pc actual,(located fetch).2]

theorem sync_fetch {s : NativeGuard.State 256} (phase : s.pending thread=false)
    (fetch : program[(s.core.lanes thread).pc]?=some (.sync resource)) :
    code[pc s thread]?=some (.sync resource) := by
  simpa [pc,phase] using (located fetch).1

theorem sync_release {s : NativeGuard.State 256} {cfg : Config 256}
    (ready : NativeGuard.Ready program s) (aligned : Aligned s.core)
    (fetch : program[(s.core.lanes thread).pc]?=some (.sync resource))
    (released : (Ptx.Barrier.step (barrierConfig cfg s.core thread) s.core.barrier
      (barrierRequest cfg s.core thread resource)).disposition=.released) :
    ∀ u, pc {s with core:=(synchronize cfg s.core thread resource).state} u=pc s u+1 := by
  intro u
  have same := release_aligned cfg s.core thread resource aligned released u
  have notPending : s.pending u=false := by
    cases phase : s.pending u with
    | false => rfl
    | true =>
      obtain ⟨_,count,target,found,_⟩ := ready.1 u phase
      rw [same,fetch] at found
      cases found
  have advancePC := (located fetch).2
  simp only [pc,synchronize,released,notPending,Bool.false_eq_true,↓reduceIte,
    advance,same,Nat.add_zero,advancePC]

end PtxTorchLean.Poisson.PTX.Concurrent.Reduction.Native

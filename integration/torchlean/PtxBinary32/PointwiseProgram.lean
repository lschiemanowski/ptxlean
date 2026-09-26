import PtxBinary32.DenseAddress
import PtxBinary32.ParallelCoverage
import PtxBinary32.ParallelAdmission
import PtxBinary32.ParallelLoadControl
import PtxBinary32.ParallelStoreControl
import PtxBinary32.ParallelWriteValues

/-! Independent pointwise lanes. Entry pointers are a checked storage interface;
loads, arithmetic, gating and stores are fetched instructions. The shared arena
is unused. Source words and destination words occupy disjoint regions. -/
namespace Ptx.Scalar.Parallel.Pointwise
open Ptx.Binary32

inductive Op where
  | copy | mul | gate
  deriving DecidableEq, Repr

def localOp (op : Scalar.Op) : Instr := .localStep (.plain op)
def clear : Instr := .localStep ⟨.pred 1 true,.mov32 6 (.imm 0)⟩
def body : Op → List Instr
  | .copy => [localOp (.mov32 6 (.reg 5))]
  | .mul => [.binary32 ⟨.always,.mul,6,.reg 4,.reg 5⟩]
  | .gate => [localOp (.mov32 6 (.reg 5)),localOp (.setp .eq 1 (.reg 4) (.imm 0)),clear,
      localOp (.setp .ge 1 (.reg 4) (.imm 0x80000000)),clear]

def program (op : Op) : List Instr :=
  [.memory .global (.plain (.load 4 (.reg 0))),.memory .global (.plain (.load 5 (.reg 1)))] ++
    body op ++ [.memory .global (.plain (.store (.reg 2) (.reg 6))),.exit]

def storePC (op : Op) : Nat := 2+(body op).length

def Result (op : Op) (a b value : Word) : Prop :=
  match op with
  | .copy => value=b
  | .mul => Results .mul a b value
  | .gate => value=Relu.gate a b

def reference (op : Op) (a b : Word) : Word :=
  match op with
  | .copy => b
  | .mul => Ptx.Binary32.reference .mul a b
  | .gate => Relu.gate a b

theorem reference_result (op : Op) (a b : Word) : Result op a b (reference op a b) := by
  cases op <;> first | rfl | exact envelope_self _

/-- The source prefix is read-only; each lane has one distinct output word. -/
structure Layout (n : Nat) where
  prefixWords : Nat
  left : Fin n → Nat
  right : Fin n → Nat
  leftBound : ∀ t, left t<prefixWords
  rightBound : ∀ t, right t<prefixWords
  small : prefixWords+n<2^30

def Layout.output (l : Layout n) (t : Fin n) := l.prefixWords+t.val

def seed (l : Layout n) (seeds : Fin n → Scalar.State) (t : Fin n) : Scalar.State :=
  {seeds t with pc := 0,addrs := fun r =>
    if r=0 then Dense.bytePointer (l.left t) else
    if r=1 then Dense.bytePointer (l.right t) else
    if r=2 then Dense.bytePointer (l.output t) else (seeds t).addrs r}

def initial (l : Layout n) (global shared : List Word) (seeds : Fin n → Scalar.State) : State n :=
  ⟨fun t => ⟨seed l seeds t,false⟩,global,shared,Barrier.reset 0,none⟩

def config (positive : 0<n) : Config n := ⟨⟨94,70⟩,0,positive⟩

theorem length_program (op : Op) : (program op).length=storePC op+2 := by
  cases op <;> rfl

theorem straight (op : Op) : Control.Straight (program op) := by
  intro i member
  cases op <;> simp [program,body,localOp,clear] at member
  all_goals repeat' (first | (rcases member with rfl | member) | (subst i; trivial))

  all_goals trivial

end Ptx.Scalar.Parallel.Pointwise

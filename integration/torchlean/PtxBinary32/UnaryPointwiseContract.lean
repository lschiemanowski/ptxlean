import PtxBinary32.SoftmaxMemory
import PtxBinary32.SoftmaxStorage

/-! Shared arithmetic and array postcondition of sequential and parallel unary
passes. This is not an execution relation: a machine must prove this contract
from its actual instructions and, for concurrent reads, memory admission. -/
namespace Ptx.Scalar.UnaryPointwise

inductive Op where
  | shifted | normalize
  deriving DecidableEq, Repr

def target : Target := ⟨94,70⟩

def Result : Op → Word → Word → Word → Prop
  | .shifted => SoftmaxMemory.ShiftedStages
  | .normalize => SoftmaxMemory.NormalizeStages

/-- Own-cell inputs and outputs occupy the prefix. The common scalar is outside
that prefix, and the whole allocated arena has nonwrapping byte addresses. -/
def Bounds (n common : Nat) (before : List Word) : Prop :=
  0<n ∧ n≤1024 ∧ n≤common ∧ common<before.length ∧ before.length<2^62

def Spec (op : Op) (n common : Nat) (before after : List Word) : Prop :=
  after.length=before.length ∧
  (∀j, n≤j → after[j]?=before[j]?) ∧
  ∀i : Fin n, Result op before[i.val]! before[common]! after[i.val]!

def sequentialStep (op : Op) (common i : Nat) : List Word → List Word → Prop :=
  match op with
  | .shifted => SoftmaxMemory.ShiftLaunch target i common i
  | .normalize => SoftmaxMemory.NormalizeLaunch target i common i

theorem sequential_writes (op : Op) (common : Nat) :
    SoftmaxSweep.WritesOwn (sequentialStep op common) := by
  intro i a b run
  cases op with
  | shifted => obtain ⟨out,_,eq⟩ := SoftmaxMemory.shifted_launch_correct run; exact ⟨out,eq⟩
  | normalize => obtain ⟨out,_,eq⟩ := SoftmaxMemory.normalize_launch_correct run; exact ⟨out,eq⟩

theorem sequential_spec (op : Op) (n common : Nat) (before after : List Word)
    (bounds : Bounds n common before)
    (run : SoftmaxSweep.Run (sequentialStep op common) n before after) :
    Spec op n common before after := by
  refine ⟨SoftmaxSweep.length (sequential_writes op common) run,
    fun j hj => SoftmaxSweep.outside (sequential_writes op common) run j hj,?_⟩
  refine SoftmaxStorage.pass_relations (relation:=Result op) (denominator:=common) ?_ run ?_ ?_
  · intro i a b h
    cases op with
    | shifted => exact SoftmaxMemory.shifted_launch_correct h
    | normalize => exact SoftmaxMemory.normalize_launch_correct h
  · exact le_trans bounds.2.2.1 bounds.2.2.2.1.le
  · exact bounds.2.2.1

end Ptx.Scalar.UnaryPointwise

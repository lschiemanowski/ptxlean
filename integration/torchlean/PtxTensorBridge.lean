import Ptx
import NN.Spec.Core.Tensor.Constructors
import Mathlib.Basic.Real.Basic

/-!
A tensor view of the existing disjoint global-memory vector-add execution.
`SharedVector` means an allocation shared by threads, not the PTX shared address
space. This module interprets 32-bit words as unsigned integers, then as exact
reals; it gives no floating-point, GPU scheduler, or PyTorch guarantee.
-/
namespace PtxTorchLean.TensorBridge
open Spec TorchLean Ptx Ptx.Scalar
noncomputable section

/-- A reusable one-dimensional layout view with an explicit scalar decoder.
Like the underlying execution's lookup, this total function uses a default for
an absent cell. Every execution theorem below supplies allocation bounds; the
view alone makes no claim that its selected cells exist. -/
def view {α : Type} [Storage α] (decode : Word → α) (memory : List Word)
    (layout : Fin n → Nat) : Tensor α [n] :=
  Tensor.ofFn fun i => decode memory[layout i]!

@[simp] theorem view_apply {α : Type} [Storage α] (decode : Word → α)
    (memory : List Word) (layout : Fin n → Nat) (i : Fin n) :
    view decode memory layout (i, PUnit.unit) = decode memory[layout i]! := by
  simp [view]

/-- Mapping the scalar interpretation preserves the selected memory layout. -/
theorem view_map {α β : Type} [Storage α] [Storage β] (decode : Word → α)
    (f : α → β) (memory : List Word) (layout : Fin n → Nat) :
    Tensor.map f (view decode memory layout) = view (f ∘ decode) memory layout := by
  apply Tensor.Internal.Rep.ext
  intro i
  simp [Tensor.map, Tensor.Internal.Rep.map_apply, view]

def unsignedView (memory : List Word) (layout : Fin n → Nat) : Tensor Nat [n] :=
  view BitVec.toNat memory layout

def realView (memory : List Word) (layout : Fin n → Nat) : Tensor ℝ [n] :=
  view (fun w => (w.toNat : ℝ)) memory layout

/-- All three selected words exist, including the initial output cell. -/
theorem layout_bounds (memory : List Word) (extent : 3*n ≤ memory.length)
    (i : Fin n) :
    SharedVector.left i < memory.length ∧ SharedVector.right i < memory.length ∧ SharedVector.output i < memory.length := by
  have := i.isLt
  simp only [SharedVector.left, SharedVector.right, SharedVector.output]
  omega

/-- The real view embeds the unsigned tensor exactly, without rounding. -/
theorem realView_eq_map (memory : List Word) (layout : Fin n → Nat) :
    realView memory layout = Tensor.map (fun v : Nat => (v : ℝ)) (unsignedView memory layout) := by
  exact (view_map BitVec.toNat (fun v : Nat => (v : ℝ)) memory layout).symm

/-- Correctness for every completed schedule of the existing execution function.
Pointer non-wrapping is separately required by the instruction-faithfulness
and execution-existence theorems, not by this mathematical schedule identity. -/
theorem completed_unsigned (memory : List Word) (registers : Fin n → Nat → Word)
    (extent : 3*n ≤ memory.length) (dispatches : List (Fin n))
    (completed : SharedVector.Complete (SharedVector.execute dispatches (SharedVector.initial memory registers))) (i : Fin n) :
    unsignedView (n:=n) (SharedVector.execute dispatches (SharedVector.initial memory registers)).memory SharedVector.output (i, PUnit.unit) =
      (unsignedView memory SharedVector.left (i, PUnit.unit) +
       unsignedView memory SharedVector.right (i, PUnit.unit)) % 2^32 := by
  simp only [unsignedView, view, Tensor.ofFn_apply]
  rw [SharedVector.completed_correct memory registers extent dispatches completed i]
  exact BitVec.toNat_add _ _

/-- The entire output tensor is pointwise unsigned addition followed by modulo. -/
theorem completed_unsigned_tensor (memory : List Word) (registers : Fin n → Nat → Word)
    (extent : 3*n ≤ memory.length) (dispatches : List (Fin n))
    (completed : SharedVector.Complete (SharedVector.execute dispatches (SharedVector.initial memory registers))) :
    unsignedView (n:=n) (SharedVector.execute dispatches (SharedVector.initial memory registers)).memory SharedVector.output =
      Tensor.map (fun v : Nat => v % 2^32) (unsignedView memory SharedVector.left + unsignedView memory SharedVector.right) := by
  apply Tensor.Internal.Rep.ext
  intro i
  obtain ⟨i, ⟨⟩⟩ := i
  simpa only [Tensor.map, Tensor.Internal.Rep.map_apply, Tensor.add_apply] using
    completed_unsigned memory registers extent dispatches completed i

/-- An input-only condition; it neither restricts the primary modular theorem
nor assumes any property of the returned output. -/
def NoOverflow (n : Nat) (memory : List Word) : Prop :=
  ∀ i : Fin n, memory[SharedVector.left i]!.toNat + memory[SharedVector.right i]!.toNat < 2^32

/-- Actual TorchLean real-tensor addition agrees exactly when input sums fit. -/
theorem completed_real_add (memory : List Word) (registers : Fin n → Nat → Word)
    (extent : 3*n ≤ memory.length) (dispatches : List (Fin n))
    (completed : SharedVector.Complete (SharedVector.execute dispatches (SharedVector.initial memory registers)))
    (fits : NoOverflow n memory) :
    realView (n:=n) (SharedVector.execute dispatches (SharedVector.initial memory registers)).memory SharedVector.output =
      realView memory SharedVector.left + realView memory SharedVector.right := by
  apply Tensor.Internal.Rep.ext
  intro i
  obtain ⟨i, ⟨⟩⟩ := i
  simp only [realView, view, Tensor.ofFn_apply, Tensor.add_apply]
  rw [SharedVector.completed_correct memory registers extent dispatches completed i]
  simp only [SharedVector.sum, BitVec.toNat_add, Nat.mod_eq_of_lt (fits i), Nat.cast_add]

/-- Every selected final cell exists; the allocation has not changed size. -/
theorem completed_bounds (memory : List Word) (registers : Fin n → Nat → Word)
    (extent : 3*n ≤ memory.length) (dispatches : List (Fin n)) (i : Fin n) :
    SharedVector.left i < (SharedVector.execute dispatches (SharedVector.initial memory registers)).memory.length ∧
    SharedVector.right i < (SharedVector.execute dispatches (SharedVector.initial memory registers)).memory.length ∧
    SharedVector.output i < (SharedVector.execute dispatches (SharedVector.initial memory registers)).memory.length := by
  rw [(SharedVector.execute_invariant memory _ extent (SharedVector.initial_invariant ..) dispatches).length]
  exact layout_bounds memory extent i

/-- Interpret the candidate's store events as a tensor. Candidates remain the
existing six-event-per-lane family; this does not invent a general PTX graph. -/
def candidateOutput (memory : List Word) (left right : Fin n → Word)
    (source : Fin (6*n) → Fin (6*n)) (co : Fin (6*n) → Fin (6*n) → Bool) : Tensor Nat [n] :=
  Tensor.ofFn fun i =>
    ((SharedVectorMemory.graph memory left right source co).event
      (SharedVectorMemory.indexOf i 5)).effect.value.toNat

/-- Source compatibility alone forces the original input values, independently
of the candidate's chosen coherence relation. Allocation bounds are required
when relating this graph-level statement to instruction execution. -/
theorem candidate_unsigned_tensor (memory : List Word) (left right : Fin n → Word) (source co)
    (sources : (SharedVectorMemory.graph memory left right source co).Sources) :
    candidateOutput memory left right source co =
      Tensor.map (fun v : Nat => v % 2^32)
        (unsignedView memory SharedVector.left + unsignedView memory SharedVector.right) := by
  apply Tensor.Internal.Rep.ext
  intro i
  obtain ⟨i, ⟨⟩⟩ := i
  simp only [candidateOutput, Tensor.ofFn_apply, Tensor.map,
    Tensor.Internal.Rep.map_apply, Tensor.add_apply, unsignedView, view]
  rw [SharedVectorMemory.candidate_output memory left right source co sources i]
  exact BitVec.toNat_add _ _

/-- Every source-compatible candidate returns the same tensor as every completed
schedule in this restricted execution family; relations need not be identical. -/
theorem candidate_execution_agree (memory : List Word) (left right : Fin n → Word) (source co)
    (sources : (SharedVectorMemory.graph memory left right source co).Sources)
    (registers : Fin n → Nat → Word) (extent : 3*n ≤ memory.length)
    (dispatches : List (Fin n))
    (completed : SharedVector.Complete (SharedVector.execute dispatches (SharedVector.initial memory registers))) :
    candidateOutput memory left right source co =
      unsignedView (n:=n) (SharedVector.execute dispatches (SharedVector.initial memory registers)).memory
        SharedVector.output := by
  rw [candidate_unsigned_tensor memory left right source co sources,
    completed_unsigned_tensor memory registers extent dispatches completed]

/-- A concrete finite instruction execution, its tensor result, preserved memory,
access safety, and a full valid memory witness with matching labels. No desired
result, successful execution, or read-source choice is an input hypothesis. -/
theorem execution_exists (memory : List Word) (registers : Fin n → Nat → Word)
    (extent : 3*n ≤ memory.length) (noWrap : 12*n < 2^64) :
    ∃ dispatches : List (Fin n),
      dispatches.length = 5*n ∧
      SharedVector.Execution dispatches (SharedVector.initial memory registers)
        (SharedVector.execute dispatches (SharedVector.initial memory registers)) ∧
      SharedVector.Complete (SharedVector.execute dispatches (SharedVector.initial memory registers)) ∧
      unsignedView (n:=n) (SharedVector.execute dispatches (SharedVector.initial memory registers)).memory
          SharedVector.output =
        Tensor.map (fun v : Nat => v % 2^32)
          (unsignedView memory SharedVector.left + unsignedView memory SharedVector.right) ∧
      (∀ index, (∀ lane : Fin n, SharedVector.output lane ≠ index) →
        (SharedVector.execute dispatches (SharedVector.initial memory registers)).memory[index]? = memory[index]?) ∧
      (∀ event ∈ SharedVector.trace dispatches (SharedVector.initial memory registers),
        AccessSafe memory.length event.effect) ∧
      (SharedVectorMemory.witness (n:=n) memory).Valid ∧
      (∀ lane : Fin n, SharedVector.laneTrace lane
        (SharedVector.trace dispatches (SharedVector.initial memory registers)) =
        [(SharedVectorMemory.witness memory).event (SharedVectorMemory.indexOf lane 3),
         (SharedVectorMemory.witness memory).event (SharedVectorMemory.indexOf lane 4),
         (SharedVectorMemory.witness memory).event (SharedVectorMemory.indexOf lane 5)]) := by
  obtain ⟨dispatches, length, faithful, complete, _, valid, labels⟩ :=
    SharedVectorMemory.verified_shared_execution memory registers extent noWrap
  refine ⟨dispatches, length, faithful, complete,
    completed_unsigned_tensor memory registers extent dispatches complete, ?_, ?_, valid, labels⟩
  · exact fun index apart => SharedVector.execute_frame _ dispatches index apart
  · exact fun event member => SharedVector.trace_access_safe memory _ dispatches extent noWrap
      (SharedVector.initial_invariant ..) event member

/-- The real-valued corollary also has an execution witness; the no-overflow
condition supplements rather than replaces allocation and pointer bounds. -/
theorem real_execution_exists (memory : List Word) (registers : Fin n → Nat → Word)
    (extent : 3*n ≤ memory.length) (noWrap : 12*n < 2^64) (fits : NoOverflow n memory) :
    ∃ dispatches : List (Fin n),
      dispatches.length = 5*n ∧
      SharedVector.Execution dispatches (SharedVector.initial memory registers)
        (SharedVector.execute dispatches (SharedVector.initial memory registers)) ∧
      SharedVector.Complete (SharedVector.execute dispatches (SharedVector.initial memory registers)) ∧
      realView (n:=n) (SharedVector.execute dispatches (SharedVector.initial memory registers)).memory
          SharedVector.output = realView memory SharedVector.left + realView memory SharedVector.right ∧
      (∀ index, (∀ lane : Fin n, SharedVector.output lane ≠ index) →
        (SharedVector.execute dispatches (SharedVector.initial memory registers)).memory[index]? = memory[index]?) := by
  obtain ⟨dispatches, length, faithful, complete, _, frame, _⟩ :=
    execution_exists memory registers extent noWrap
  exact ⟨dispatches, length, faithful, complete,
    completed_real_add memory registers extent dispatches complete fits, frame⟩

/-- The decoder reads an actual existing cell when the layout bound is supplied;
no default-value behavior participates in that bounded lookup. -/
theorem view_bounded_apply {α : Type} [Storage α] (decode : Word → α)
    (memory : List Word) (layout : Fin n → Nat) (i : Fin n)
    (bound : layout i < memory.length) :
    view decode memory layout (i, PUnit.unit) = decode memory[layout i] := by
  simp [view, bound]

/-- A direct evaluation of the actual five-instruction schedule: the largest
u32 plus one stores zero. Arbitrary output initialization is overwritten. -/
theorem wraparound_execution :
    unsignedView (n:=1)
      (SharedVector.execute [0,0,0,0,0]
        (SharedVector.initial [BitVec.ofNat 32 4294967295, 1, 73]
          (fun (_ : Fin 1) _ => 19))).memory SharedVector.output (0, PUnit.unit) = 0 := by
  decide

/-- The same overflowing inputs deliberately fail the real-addition condition. -/
theorem wraparound_not_fitting :
    ¬NoOverflow 1 [BitVec.ofNat 32 4294967295, 1, 73] := by
  intro h
  have bad := h 0
  norm_num [SharedVector.left, SharedVector.right] at bad

-- Audit every public theorem, including the direct execution boundary checks.
#print axioms view_apply
#print axioms view_map
#print axioms layout_bounds
#print axioms realView_eq_map
#print axioms completed_unsigned
#print axioms completed_unsigned_tensor
#print axioms completed_real_add
#print axioms completed_bounds
#print axioms candidate_unsigned_tensor
#print axioms candidate_execution_agree
#print axioms execution_exists
#print axioms real_execution_exists
#print axioms view_bounded_apply
#print axioms wraparound_execution
#print axioms wraparound_not_fitting

end
end PtxTorchLean.TensorBridge

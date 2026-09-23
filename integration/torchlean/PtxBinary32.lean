import Ptx.Language
import NN.Floats.IEEEExec.Bridge.Finite
import NN.Floats.FP32.Error

/-! Payload-preserving encoded binary32 and a conservative NaN-result envelope.
This is a numerical foundation, not fetched PTX instruction semantics. The
reference is checked software arithmetic; no host floating-point primitive is
used. Finiteness remains an explicit premise of every real-error result. -/
namespace Ptx.Binary32

open FloatLib.Floats (ExecFloat)
open FloatLib.Floats.ExecFloat (Binary)
open FloatLib.Floats.Formats.BinaryInterchange (Model FloatFormat)
open TorchLean.Floats.IEEE754.IEEE32Exec

abbrev Value := ExecFloat.Binary 8 23

def decode (word : Word) : Value := Binary.ofBits32 (UInt32.ofBitVec word)
def encode (value : Value) : Word := (Binary.toBits32 value).toBitVec

@[simp] theorem encode_decode (word : Word) : encode (decode word) = word := rfl
@[simp] theorem decode_encode (value : Value) : decode (encode value) = value := by
  simp [decode, encode]

def isNaN (word : Word) : Bool := Binary.isNaN (decode word)
def isFinite (word : Word) : Bool := Binary.isFinite (decode word)

/-- No exceptional encoding is silently interpreted as real zero by this API. -/
noncomputable def finiteReal (word : Word) : Option ℝ :=
  if isFinite word then some (Binary.toModel (decode word)).toReal else none

theorem finiteReal_none (word : Word) (h : isFinite word = false) :
    finiteReal word = none := by simp [finiteReal, h]

theorem finiteReal_some (word : Word) (h : isFinite word = true) :
    finiteReal word = some (Binary.toModel (decode word)).toReal := by simp [finiteReal, h]

theorem finiteReal_isSome (word : Word) : (finiteReal word).isSome = isFinite word := by
  simp [finiteReal]; split <;> simp_all

theorem finite_not_nan (word : Word) (h : isFinite word = true) : isNaN word = false :=
  Model.isNaN_eq_false_of_isFinite_eq_true (Binary.toModel (decode word)) h

/-- Conservative over-approximation: NaN bit realizability is not asserted. -/
def Envelope (reference output : Word) : Prop :=
  if isNaN reference then isNaN output = true else output = reference

instance (reference output : Word) : Decidable (Envelope reference output) := by
  unfold Envelope; infer_instance

theorem envelope_self (reference : Word) : Envelope reference reference := by
  unfold Envelope; split <;> simp_all

theorem envelope_exists (reference : Word) : ∃ output, Envelope reference output :=
  ⟨reference, envelope_self reference⟩

theorem envelope_nan (reference output : Word) (h : isNaN reference = true) :
    Envelope reference output ↔ isNaN output = true := by simp [Envelope, h]

theorem envelope_non_nan (reference output : Word) (h : isNaN reference = false) :
    Envelope reference output ↔ output = reference := by simp [Envelope, h]

theorem envelope_finite_eq (reference output : Word) (h : isFinite reference = true)
    (allowed : Envelope reference output) : output = reference :=
  (envelope_non_nan reference output (finite_not_nan reference h)).mp allowed

theorem envelope_finite (reference output : Word) (h : isFinite reference = true)
    (allowed : Envelope reference output) : isFinite output = true := by
  rw [envelope_finite_eq reference output h allowed]; exact h

/-- Selected reference operations; this enum is not a PTX decoder. -/
inductive Operation where
  | add | mul
  deriving DecidableEq, Repr

def reference (op : Operation) (left right : Word) : Word :=
  encode (match op with
    | .add => ExecFloat.add (decode left) (decode right)
    | .mul => ExecFloat.mul (decode left) (decode right))

def Results (op : Operation) (left right output : Word) : Prop :=
  Envelope (reference op left right) output

theorem results_exists (op : Operation) (left right : Word) :
    ∃ output, Results op left right output := envelope_exists _

/-- The real target is used only under explicit finite operand hypotheses. -/
noncomputable def exact (op : Operation) (left right : Word) : ℝ :=
  match op with
  | .add => (Binary.toModel (decode left)).toReal + (Binary.toModel (decode right)).toReal
  | .mul => (Binary.toModel (decode left)).toReal * (Binary.toModel (decode right)).toReal

theorem reference_round (op : Operation) (left right : Word)
    (finite : isFinite (reference op left right) = true) :
    (Binary.toModel (decode (reference op left right))).toReal =
      fp32Round (exact op left right) := by
  cases op with
  | add =>
    simpa [reference, isFinite, exact] using
      (toReal_add_eq_fp32Round_of_isFinite (x := decode left) (y := decode right)
        (by simpa [reference, isFinite] using finite))
  | mul =>
    simpa [reference, isFinite, exact] using
      (toReal_mul_eq_fp32Round_of_isFinite (x := decode left) (y := decode right)
        (by simpa [reference, isFinite] using finite))

/-- This covers all outputs in the envelope, not only the reference witness.
The actual encoded result-finiteness obligation remains visible. -/
theorem results_round (op : Operation) (left right output : Word)
    (finite : isFinite (reference op left right) = true)
    (allowed : Results op left right output) :
    finiteReal output = some (fp32Round (exact op left right)) := by
  have eq := envelope_finite_eq _ _ finite allowed
  subst output
  rw [finiteReal_some _ finite, reference_round op left right finite]

/-- Explicit real operands avoid any interpretation of exceptional inputs as
zero. Finiteness of the encoded result must be established by the consumer. -/
theorem results_abs_error (op : Operation) (left right output : Word) (x y : ℝ)
    (leftReal : finiteReal left = some x) (rightReal : finiteReal right = some y)
    (finite : isFinite (reference op left right) = true)
    (allowed : Results op left right output) :
    ∃ z : ℝ, finiteReal output = some z ∧
      |z - (match op with | .add => x + y | .mul => x * y)| ≤
        TorchLean.Floats.eps32 (match op with | .add => x + y | .mul => x * y) := by
  have leftEq : (Binary.toModel (decode left)).toReal = x := by
    unfold finiteReal at leftReal
    split at leftReal <;> simp_all
  have rightEq : (Binary.toModel (decode right)).toReal = y := by
    unfold finiteReal at rightReal
    split at rightReal <;> simp_all
  refine ⟨fp32Round (exact op left right), results_round op left right output finite allowed, ?_⟩
  have bound := TorchLean.Floats.FP32.round_abs_error (exact op left right)
  cases op <;> simpa [exact, leftEq, rightEq, fp32Round, TorchLean.Floats.round32] using bound

end Ptx.Binary32

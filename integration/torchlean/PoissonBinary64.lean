import PoissonQuad
import Mathlib.Algebra.BigOperators.Group.List.Basic

/-! Logical binary64 arithmetic used by the Poisson correspondence lemmas.
Lean 4.34's `Float` has a kernel-visible IEEE model; these proofs do not use
native_decide or assert anything about an external compiler/GPU. NaN payloads
are canonicalized by this logical carrier. -/
namespace PtxTorchLean.Poisson.Binary64
open Float.Model

private theorem sign_mul_comm (x y : UnpackedFloat.Sign) : x*y=y*x := by
  cases x <;> cases y <;> rfl

theorem unpacked_mul_comm (x y : UnpackedFloat) :
    UnpackedFloat.mul Format.binary64 x y = UnpackedFloat.mul Format.binary64 y x := by
  cases x <;> cases y <;>
    simp [UnpackedFloat.mul, Nat.mul_comm, Int.add_comm, sign_mul_comm]

/-- Operand reversal in the PTX weight multiplication preserves the canonical
logical binary64 value, including exceptional classifications. This does not
claim a particular hardware NaN payload. -/
theorem mul_comm (x y : Float) : x*y=y*x := by
  change Float.ofModel (Float.Model.pack _) = Float.ofModel (Float.Model.pack _)
  rw [unpacked_mul_comm]

/-- The eight shared-memory halving rounds in the 256-lane dot-product kernel. -/
def round (stride : Nat) (s : Nat → Float) : Nat → Float :=
  fun i => if i < stride then s i + s (i+stride) else s i

def reduce256 (s : Nat → Float) : Float :=
  (([128,64,32,16,8,4,2,1] : List Nat).foldl (fun values stride => round stride values) s) 0

/-- Four exactly representable values; all other lane partial sums are +0. -/
def cancellation : Nat → Float
  | 0 => Float.ofBits 0x4340000000000000 -- 2^53
  | 1 => Float.ofBits 0x3ff0000000000000 -- 1
  | 2 => Float.ofBits 0xc340000000000000 -- -2^53
  | 3 => Float.ofBits 0x3ff0000000000000 -- 1
  | _ => Float.ofBits 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
/-- Kernel-checked concrete refutation of universal CPU/GPU reduction equality.
These are exact logical binary64 computations, not native numerical tests. -/
theorem reduction_order_counterexample :
    (([0,1,2,3] : List Nat).foldl (fun acc i => acc + cancellation i) (Float.ofBits 0)).toBits =
      0x3ff0000000000000 ∧
    (reduce256 cancellation).toBits = 0x4000000000000000 := by
  decide

end PtxTorchLean.Poisson.Binary64

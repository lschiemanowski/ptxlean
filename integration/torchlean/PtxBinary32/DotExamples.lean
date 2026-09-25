import PtxBinary32.DotError

/-! Kernel-checked boundaries: empty input, ignored initial accumulator, and
rounding-sensitive order. These are software-model examples, not GPU tests. -/
namespace Ptx.Scalar.Dot.Examples
open Mixed

set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

private def referenceFold : List (Word × Word) → Word → Word
  | [], acc => acc
  | x::xs, acc => referenceFold xs (Ptx.Binary32.reference .add
      (Ptx.Binary32.reference .mul x.1 x.2) acc)

private def ordinary : List (Word × Word) → Word → Bool
  | [], _ => true
  | x::xs, acc =>
    let p := Ptx.Binary32.reference .mul x.1 x.2
    let q := Ptx.Binary32.reference .add p acc
    Ptx.Binary32.isFinite p && Ptx.Binary32.isFinite q && ordinary xs q

private theorem exact_fold (xs : List (Word × Word)) (acc out : Word)
    (finite : ordinary xs acc = true) (allowed : Fold xs acc out) :
    out = referenceFold xs acc := by
  induction allowed with
  | nil => rfl
  | @cons x acc p q xs out pair tail ih =>
    simp only [ordinary,Bool.and_eq_true] at finite
    have hp := Ptx.Binary32.envelope_finite_eq _ _ finite.1.1 pair.1
    subst p
    have hq := Ptx.Binary32.envelope_finite_eq _ _ finite.1.2 pair.2
    subst q
    exact ih finite.2

/-- 2^24 + 1 - 2^24 loses the middle term under left-to-right binary32 addition. -/
def cancellation : List (Word × Word) :=
  [(0x4b800000,0x3f800000),(0x3f800000,0x3f800000),(0xcb800000,0x3f800000)]

/-- The same products in a different order produce one instead. -/
def reordered : List (Word × Word) :=
  [(0x4b800000,0x3f800000),(0xcb800000,0x3f800000),(0x3f800000,0x3f800000)]

theorem cancellation_result (allowed : Fold cancellation 0 out) : out = 0 := by
  have h := exact_fold cancellation 0 out (by decide) allowed
  exact h.trans (by decide)

theorem reordered_result (allowed : Fold reordered 0 out) : out = 0x3f800000 := by
  have h := exact_fold reordered 0 out (by decide) allowed
  exact h.trans (by decide)

/-- The empty kernel overwrites the output with positive zero regardless of
initial register or scratch values. It still performs its store and exit. -/
theorem empty_result (s : State) (outBound : output < s.memory.length)
    (outPointer : 4*output < 2^64)
    (run : Run target program (initial s 0 0 output 0) final status events) :
    status = .halted ∧ events.length = 5 ∧ final.memory = s.memory.set output 0 := by
  have bounds : Bounds s.memory 0 0 [] := by constructor <;> simp
  have stored : Stored s.memory 0 0 [] := by intro i x h; simp at h
  obtain ⟨hs,len,out,fold,mem⟩ := correct bounds stored outBound outPointer run
  cases fold
  exact ⟨hs,len,mem⟩

/-- Cancellation example is an actual finite instruction execution, with
nonzero initial registers and arbitrary initial output storage. -/
def cancellationState : State :=
  ⟨57,fun _ => 0xdeadbeef,fun _ => 0,fun _ => true,
    [0x4b800000,0x3f800000,0xcb800000,0x3f800000,0x3f800000,0x3f800000,0xdeadbeef]⟩

private theorem cancellation_stored : Stored cancellationState.memory 0 3 cancellation := by
  intro i x h
  have bound : i < 3 := (List.getElem?_eq_some_iff.mp h).choose
  interval_cases i <;> simp [cancellation] at h <;> subst x <;> decide

private theorem cancellation_bounds : Bounds cancellationState.memory 0 3 cancellation := by
  constructor <;> decide

theorem cancellation_execution (eligible : Eligible target) :
    ∃ final events, Run target program (initial cancellationState 0 3 6 3) final .halted events ∧
      events.length = 35 ∧ final.memory = cancellationState.memory.set 6 0 := by
  obtain ⟨final,events,run,len,out,fold,mem⟩ := execution_exists eligible cancellation_bounds
    cancellation_stored (output := 6) (by decide) (by decide)
  rw [cancellation_result fold] at mem
  exact ⟨final,events,run,len,mem⟩

/-- The numerical domain has a concrete nonempty inhabitant with exact encodings. -/
noncomputable def zeroInput : Ptx.Binary32.DotError.Input where
  left := 0
  right := 0
  lh := 0
  rh := 0
  l := 0
  r := 0
  el := 0
  er := 0
  leftReal := Ptx.Binary32.SquareError.zero_real
  rightReal := Ptx.Binary32.SquareError.zero_real
  leftError := by simp
  rightError := by simp
  productRange := by norm_num [Ptx.Binary32.Bounds.maxFinite_eq]

theorem nonempty_numerical_domain : Ptx.Binary32.DotError.Safe [zeroInput] 0 := by
  change |(0:ℝ)*0| + TorchLean.Floats.eps32 (0*0) + |0| ≤ Ptx.Binary32.Bounds.maxFinite ∧ True
  simp only [zero_mul,abs_zero,zero_add,add_zero,and_true]
  change TorchLean.Floats.ulp32 0 / 2 ≤ Ptx.Binary32.Bounds.maxFinite
  rw [TorchLean.Floats.ulp32_zero,Ptx.Binary32.Bounds.maxFinite_eq]
  norm_num [FloatLib.Floats.Formats.Flocq.bpow,
    FloatLib.Numerics.binaryRadix,FloatLib.Numerics.Radix.toReal]

end Ptx.Scalar.Dot.Examples

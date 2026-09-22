import Ptx.ByteMemory

/-! Actual normalized constant-store programs exhibiting byte-source tearing.
Every admissibility and impossibility result is proved under both explicitly
represented observation policies. These examples contain no dependent stores. -/
namespace Ptx.ByteExamples

/-- One initialized word, one complete program write, and one complete read. -/
def program (written : Word) : Program :=
  ⟨[0], [[.store .relaxed 0 written], [.load .relaxed 0 0]]⟩

def registers : Nat → Registers := fun _ _ => 0
def oracle (value : Word) (tid _position : Nat) : Word := if tid = 1 then value else 0
def topology (tid : Nat) : ThreadLocation := ⟨0, 0, 0, tid, 0⟩
def scope (value : Scope) : Fin 3 → Scope := fun _ => value

/-- Read event 2 gets low-address bytes from initialization, high bytes from write1. -/
def mixedSource (r : Fin 3) (offset : Fin 4) : Fin 3 :=
  if r = 2 then if offset.val < 2 then 0 else 1 else 0

def coherence (a b : Fin 3) : Bool := a == 0 && b == 1

def candidate (written value : Word) (sc : Scope) (policy : ObservationPolicy) : ByteGraph 3 :=
  (program written).byteGraph registers (oracle value) mixedSource coherence topology (scope sc) policy

/-- Final result comes from executing the consumer load into register0. -/
def result (written value : Word) : Word :=
  (execute ((program written).threads[1]!) (registers 1) (oracle value 1)).1 0

theorem result_eq (written value : Word) : result written value = value := rfl

theorem little_endian_example :
    [wordByte 1144201745 0, wordByte 1144201745 1,
     wordByte 1144201745 2, wordByte 1144201745 3] = [17, 34, 51, 68] := by decide

/-- With mutually excluding CTA scopes, no single-copy rule forbids these mixed bytes. -/
theorem torn_valid (policy : ObservationPolicy) :
    (candidate 4294967295 4294901760 .cta policy).Valid := by
  cases policy <;> decide

/-- The source-compatible value is 0xffff0000, different from BOTH complete writes. -/
theorem torn_value_is_new :
    (4294901760 : Word) ≠ 0 ∧ (4294901760 : Word) ≠ 4294967295 := by decide

theorem torn_execution_exists (policy : ObservationPolicy) :
    (program 4294967295).ByteAdmitted registers (oracle 4294901760) mixedSource coherence
      topology (scope .cta) policy ∧ result 4294967295 4294901760 = 4294901760 := by
  refine ⟨⟨?_, ?_, torn_valid policy⟩, rfl⟩
  · simp [Program.Bounded, program, Instr.address]
  · intro i _ j _ equal
    exact congrArg ThreadLocation.cta equal

/-- Strengthening only the scopes makes the same torn source map violate the
qualified single-copy rule, independently of the observation convention. -/
theorem in_scope_torn_forbidden (policy : ObservationPolicy) :
    ¬(candidate 4294967295 4294901760 .gpu policy).Valid := by
  intro valid
  have moral : (candidate 4294967295 4294901760 .gpu policy).morallyStrong 2 1 := by
    cases policy <;> decide
  exact valid.atomicity 2 1 (by trivial) (by trivial) moral 2 rfl 0 (by rfl)

/-- The previous model cannot represent this genuinely torn numerical outcome:
its projected first-byte source supplies zero for the entire read. -/
theorem torn_projection_invalid (policy : ObservationPolicy) :
    ¬(candidate 4294967295 4294901760 .cta policy).toScoped.Valid := by
  intro valid
  have source := valid.sources.compatible 2 (by trivial)
  have impossible : (0 : Word) = 4294901760 := source.2.2
  contradiction

/-- Equal numerical values do not identify source writes. Both writes here store
zero, but the read still takes bytes from two distinct source identities. -/
theorem equal_value_not_uniform (policy : ObservationPolicy) :
    (candidate 0 0 .cta policy).Valid ∧
    ((candidate 0 0 .cta policy).event 2).effect.value =
      ((candidate 0 0 .cta policy).event 1).effect.value ∧
    ¬(candidate 0 0 .cta policy).Uniform := by
  cases policy <;> decide

/-- Every generated access still covers exactly the one valid aligned word. -/
theorem memory_safe (written value : Word) (sc : Scope) (policy : ObservationPolicy)
    (index : Fin 3) : AccessSafe 1 ((candidate written value sc policy).event index).effect := by
  apply Program.byteGraph_access_safe
  simp [Program.Bounded, program, Instr.address]

end Ptx.ByteExamples

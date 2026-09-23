import Ptx.ScalarText
import Ptx.ScalarMemoryWitness

/-! A small ordered scalar instruction layer. Order is part of the instruction
fetched at the current PC; values and addresses come from Scalar.eval. It does
not reinterpret the existing relaxed Scalar.Text language. -/
namespace Ptx.Scalar.Ordered

inductive Op where
  | mov (destination : Nat) (source : Operand32)
  | add (destination : Nat) (left right : Operand32)
  | load (order : LoadOrder) (destination : Nat) (address : Operand64)
  | store (order : StoreOrder) (address : Operand64) (sourceRegister : Nat)
  | exit
  deriving DecidableEq, Repr

structure Instr where
  guard : Guard := .always
  op : Op
  deriving DecidableEq, Repr

def Op.erase : Op → Scalar.Op
  | .mov d s => .mov32 d s
  | .add d a b => .bin32 .add d a b
  | .load _ d a => .load d a
  | .store _ a s => .store a (.reg s)
  | .exit => .exit

def Instr.erase (instruction : Instr) : Scalar.Instr :=
  ⟨instruction.guard, instruction.op.erase⟩

def erase (program : List Instr) : List Scalar.Instr := program.map Instr.erase

/-- A memory label requires a matching fetched instruction, an executed guard,
and an effect of the corresponding kind. Missing/mismatched evidence fails
closed. This function is only used on the actual run below. -/
def label (program : List Instr) (thread position : Nat)
    (occ : Scalar.Occurrence) : Option Ptx.Occurrence :=
  match program[occ.pc]?, occ.memory with
  | some instruction, some effect =>
    if occ.instruction = instruction.erase ∧ occ.executed = true then
      match instruction.op, effect.kind with
      | .load order _ _, .load =>
        some ⟨some thread, position, ⟨.load order, effect.address.toNat / 4, effect.value⟩⟩
      | .store order _ _, .store =>
        some ⟨some thread, position, ⟨.store order, effect.address.toNat / 4, effect.value⟩⟩
      | _, _ => none
    else none
  | _, _ => none

def run (fuel : Nat) (oracle : Nat → Option Word) (program : List Instr)
    (start : State) : RunResult := runWith fuel oracle (erase program) start

def events (fuel : Nat) (oracle : Nat → Option Word) (program : List Instr)
    (start : State) (thread : Nat) : List Ptx.Occurrence :=
  ((run fuel oracle program start).trace.mapIdx (label program thread)).filterMap id

theorem run_sound (fuel oracle program start) :
    Scalar.Runs (erase program) oracle start (run fuel oracle program start) :=
  runWith_sound _ _ _ _

theorem run_safe (fuel oracle program start) :
    ∀ occ ∈ (run fuel oracle program start).trace,
      ∀ effect, occ.memory = some effect → ValidAddress start.memory effect.address :=
  runWith_trace_safe _ _ _ _

theorem skipped_no_label (program thread position occ)
    (skipped : occ.executed = false) : label program thread position occ = none := by
  cases h : program[occ.pc]? <;> cases hm : occ.memory <;> simp [label, h, hm, skipped]

/-- Every emitted label retains the actual instruction occurrence and the
dispatch position. Its qualifier is selected from that instruction's opcode. -/
theorem label_origin (program thread position occ result)
    (emitted : label program thread position occ = some result) :
    ∃ instruction effect,
      program[occ.pc]? = some instruction ∧ occ.instruction = instruction.erase ∧
      occ.executed = true ∧ occ.memory = some effect ∧
      result.thread = some thread ∧ result.position = position ∧
      result.effect.address = effect.address.toNat / 4 ∧
      result.effect.value = effect.value ∧
      (match instruction.op, effect.kind with
       | .load order _ _, .load => result.effect.op = .load order
       | .store order _ _, .store => result.effect.op = .store order
       | _, _ => False) := by
  cases hf : program[occ.pc]? with
  | none => simp [label, hf] at emitted
  | some instruction =>
    cases hm : occ.memory with
    | none => simp [label, hf, hm] at emitted
    | some effect =>
      simp only [label, hf, hm] at emitted
      split at emitted
      · rename_i good
        cases hop : instruction.op <;> cases hk : effect.kind <;> simp [hop, hk] at emitted
        all_goals subst result; exact ⟨instruction, effect, rfl, good.1, good.2, rfl,
          rfl, rfl, rfl, rfl, by simp [hop, hk]⟩
      · contradiction

/-- The word-index translation loses no byte address for safe aligned accesses. -/
theorem label_byte_address (program thread position occ result)
    (emitted : label program thread position occ = some result)
    (aligned : ∀ effect, occ.memory = some effect → effect.address.toNat % 4 = 0) :
    ∃ effect, occ.memory = some effect ∧
      Ptx.byteAddress result.effect.address = effect.address.toNat := by
  obtain ⟨instruction, effect, _, _, _, hm, _, _, address, _, _⟩ :=
    label_origin _ _ _ _ _ emitted
  refine ⟨effect, hm, ?_⟩
  have division := Nat.mod_add_div effect.address.toNat 4
  simpa [Ptx.byteAddress, address, aligned effect hm] using division

/-- No successful memory step disappears during labeling: the original fetched
instruction, actual execution and memory effect provide all matching evidence. -/
theorem label_complete (program : List Instr) (thread position : Nat)
    (instruction : Instr) (s next : State) (occ : Scalar.Occurrence)
    (override : Option Word) (effect : MemoryEffect)
    (fetch : program[s.pc]? = some instruction)
    (step : Scalar.eval override instruction.erase s = .next next occ)
    (memory : occ.memory = some effect) :
    ∃ emitted, label program thread position occ = some emitted := by
  rcases instruction with ⟨guard, op⟩
  cases op <;> cases hg : guard.eval s <;>
    simp only [Instr.erase, Op.erase, Scalar.eval, hg, ↓reduceIte] at step
  all_goals first
    | (obtain ⟨_, rfl⟩ := StepResult.next.inj step; simp [occurrence] at memory)
    | contradiction
    | skip
  all_goals
    split at step
    · contradiction
    · obtain ⟨_, rfl⟩ := StepResult.next.inj step
      simp [label, occurrence, fetch, Instr.erase, Op.erase]

/-- Labels originate at an actual trace index, including gaps for arithmetic,
register moves and predicate-false instructions. -/
theorem events_origin (fuel oracle program start thread emitted)
    (member : emitted ∈ events fuel oracle program start thread) :
    ∃ position, ∃ bound : position < (run fuel oracle program start).trace.length,
      label program thread position (run fuel oracle program start).trace[position] = some emitted := by
  obtain ⟨value, mapped, same⟩ := List.mem_filterMap.mp member
  obtain ⟨position, bound, labelled⟩ := List.mem_mapIdx.mp mapped
  exact ⟨position, bound, labelled.trans same⟩

def encodeOp : Op → String × List Text.Token
  | .mov d s => ("mov.b32", [.word (.reg d), .word s])
  | .add d a b => ("add.u32", [.word (.reg d), .word a, .word b])
  | .load .relaxed d a => ("ld.relaxed.gpu.global.u32", [.word (.reg d), .memory a])
  | .load .acquire d a => ("ld.acquire.gpu.global.u32", [.word (.reg d), .memory a])
  | .store .relaxed a s => ("st.relaxed.gpu.global.u32", [.memory a, .word (.reg s)])
  | .store .release a s => ("st.release.gpu.global.u32", [.memory a, .word (.reg s)])
  | .exit => ("exit", [])

def encode (instruction : Instr) : Text.Statement :=
  ⟨instruction.guard, (encodeOp instruction.op).1, (encodeOp instruction.op).2⟩

def decodeOp : String → List Text.Token → Option Op
  | "mov.b32", [.word (.reg d), .word s] => some (.mov d s)
  | "add.u32", [.word (.reg d), .word a, .word b] => some (.add d a b)
  | "ld.relaxed.gpu.global.u32", [.word (.reg d), .memory a] => some (.load .relaxed d a)
  | "ld.acquire.gpu.global.u32", [.word (.reg d), .memory a] => some (.load .acquire d a)
  | "st.relaxed.gpu.global.u32", [.memory a, .word (.reg s)] => some (.store .relaxed a s)
  | "st.release.gpu.global.u32", [.memory a, .word (.reg s)] => some (.store .release a s)
  | "exit", [] => some .exit
  | _, _ => none

def decode (statement : Text.Statement) : Option Instr :=
  (decodeOp statement.mnemonic statement.operands).map (⟨statement.guard, ·⟩)

theorem decode_encode (instruction : Instr) : decode (encode instruction) = some instruction := by
  rcases instruction with ⟨guard, op⟩
  cases op with
  | load order d a => cases order <;> rfl
  | store order a s => cases order <;> rfl
  | _ => rfl

theorem literal_store_rejected (order : StoreOrder) (address : Operand64) (value : Word) :
    decodeOp (encodeOp (.store order address 0)).1 [.memory address, .word (.imm value)] = none := by
  cases order <;> rfl

end Ptx.Scalar.Ordered

import Ptx.Language

/-!
# A scalar machine with explicit execution outcomes

This is a concrete, sequential arena machine for a typed PTX integer subset.
Candidate reads can be supplied explicitly through `stepWith`/`runWith`; such
candidates are not automatically permitted PTX weak-memory executions. Registers
and initial memory are supplied by the caller, never implicitly initialized.
-/
namespace Ptx.Scalar

abbrev Address := BitVec 64

inductive Operand32 where
  | reg (index : Nat)
  | imm (value : Word)
  deriving DecidableEq, Repr

inductive Operand64 where
  | reg (index : Nat)
  | imm (value : Address)
  deriving DecidableEq, Repr

inductive BinOp where
  | add | sub | mulLo | and | or | xor | shl | shr | minU | maxU
  deriving DecidableEq, Repr

inductive UnaryOp where
  | clz | popc
  deriving DecidableEq, Repr

inductive Compare where
  | eq | ne | lt | le | gt | ge
  deriving DecidableEq, Repr

inductive Guard where
  | always
  | pred (index : Nat) (positive : Bool)
  deriving DecidableEq, Repr

inductive Op where
  | mov32 (destination : Nat) (source : Operand32)
  | bin32 (operation : BinOp) (destination : Nat) (left right : Operand32)
  | unary32 (operation : UnaryOp) (destination : Nat) (source : Operand32)
  | mov64 (destination : Nat) (source : Operand64)
  | add64 (destination : Nat) (left right : Operand64)
  | cvt64 (destination : Nat) (source : Operand32)
  | setp (comparison : Compare) (destination : Nat) (left right : Operand32)
  | load (destination : Nat) (address : Operand64)
  | store (address : Operand64) (source : Operand32)
  | bra (target : Nat)
  | exit
  | unsupported (spelling : String)
  deriving DecidableEq, Repr

structure Instr where
  guard : Guard := .always
  op : Op
  deriving DecidableEq, Repr

def Instr.plain (op : Op) : Instr := ⟨.always, op⟩

structure State where
  pc : Nat
  regs : Nat → Word
  addrs : Nat → Address
  preds : Nat → Bool
  memory : List Word

def update (registers : Nat → α) (destination : Nat) (value : α) : Nat → α :=
  fun index => if index = destination then value else registers index

@[simp] theorem update_same : update registers destination value destination = value := by
  simp [update]

@[simp] theorem update_other (h : index ≠ destination) :
    update registers destination value index = registers index := by simp [update, h]

def Operand32.eval (s : State) : Operand32 → Word
  | .reg index => s.regs index
  | .imm value => value

def Operand64.eval (s : State) : Operand64 → Address
  | .reg index => s.addrs index
  | .imm value => value

/-- Shift counts are unsigned 32-bit values. PTX clamps counts at 32. -/
def BinOp.eval : BinOp → Word → Word → Word
  | .add, a, b => a + b
  | .sub, a, b => a - b
  | .mulLo, a, b => a * b
  | .and, a, b => a &&& b
  | .or, a, b => a ||| b
  | .xor, a, b => a ^^^ b
  | .shl, a, b => if b.toNat < 32 then a <<< b.toNat else 0
  | .shr, a, b => if b.toNat < 32 then a >>> b.toNat else 0
  | .minU, a, b => if a.toNat ≤ b.toNat then a else b
  | .maxU, a, b => if a.toNat ≥ b.toNat then a else b

/-- PTX 9.4 `clz.b32` and `popc.b32`; their result register is u32. -/
def UnaryOp.eval : UnaryOp → Word → Word
  | .clz, a => BitVec.ofNat 32 ((List.range 32).reverse.takeWhile
      (fun i => !a.getLsbD i)).length
  | .popc, a => BitVec.ofNat 32 ((List.range 32).filter
      (fun i => a.getLsbD i)).length

def Compare.eval : Compare → Word → Word → Bool
  | .eq, a, b => a == b
  | .ne, a, b => !(a == b)
  | .lt, a, b => decide (a.toNat < b.toNat)
  | .le, a, b => decide (a.toNat ≤ b.toNat)
  | .gt, a, b => decide (a.toNat > b.toNat)
  | .ge, a, b => decide (a.toNat ≥ b.toNat)

def Guard.eval (s : State) : Guard → Bool
  | .always => true
  | .pred index positive => s.preds index == positive

inductive Register where
  | word (index : Nat)
  | address (index : Nat)
  | predicate (index : Nat)
  deriving DecidableEq, Repr

def Operand32.reads : Operand32 → List Register
  | .reg index => [.word index]
  | .imm _ => []

def Operand64.reads : Operand64 → List Register
  | .reg index => [.address index]
  | .imm _ => []

def Guard.reads : Guard → List Register
  | .always => []
  | .pred index _ => [.predicate index]

def Op.reads : Op → List Register
  | .mov32 _ source | .cvt64 _ source => source.reads
  | .bin32 _ _ left right | .setp _ _ left right => left.reads ++ right.reads
  | .unary32 _ _ source => source.reads
  | .mov64 _ source => source.reads
  | .add64 _ left right => left.reads ++ right.reads
  | .load _ address => address.reads
  | .store address source => address.reads ++ source.reads
  | .bra _ | .exit | .unsupported _ => []

def Op.writes : Op → List Register
  | .mov32 destination _ | .bin32 _ destination _ _ | .unary32 _ destination _ | .load destination _ => [.word destination]
  | .mov64 destination _ | .add64 destination _ _ | .cvt64 destination _ => [.address destination]
  | .setp _ destination _ _ => [.predicate destination]
  | .store _ _ | .bra _ | .exit | .unsupported _ => []

inductive MemoryKind where
  | load | store
  deriving DecidableEq, Repr

structure MemoryEffect where
  kind : MemoryKind
  address : Address
  value : Word
  deriving DecidableEq, Repr

/-- Direct operand/register metadata, not a completed PTX dependency semantics.
The trace order records dynamic control; skipped instructions only read their guard. -/
structure Occurrence where
  pc : Nat
  instruction : Instr
  executed : Bool
  reads : List Register
  writes : List Register
  memory : Option MemoryEffect
  deriving DecidableEq, Repr

def occurrence (s : State) (instruction : Instr) (executed : Bool)
    (memory : Option MemoryEffect := none) : Occurrence :=
  ⟨s.pc, instruction, executed,
   instruction.guard.reads ++ if executed then instruction.op.reads else [],
   if executed then instruction.op.writes else [], memory⟩

inductive Fault where
  | invalidPC (pc : Nat)
  | misaligned (address : Address)
  | outOfBounds (address : Address)
  deriving DecidableEq, Repr

inductive StepResult where
  | next (state : State) (event : Occurrence)
  | halted (state : State) (event : Occurrence)
  | fault (reason : Fault)
  | unsupported (spelling : String)

/-- Byte address validity in the caller-supplied arena. No wrapping arena extent. -/
def ValidAddress (memory : List Word) (address : Address) : Prop :=
  address.toNat % 4 = 0 ∧ address.toNat / 4 < memory.length

instance (memory : List Word) (address : Address) : Decidable (ValidAddress memory address) := by
  unfold ValidAddress; infer_instance

/-- A checked byte-to-word lookup retains the exact invalid-access reason. -/
def addressIndex (memory : List Word) (address : Address) : Except Fault Nat :=
  if address.toNat % 4 = 0 then
    if address.toNat / 4 < memory.length then .ok (address.toNat / 4)
    else .error (.outOfBounds address)
  else .error (.misaligned address)

theorem addressIndex_ok_iff : addressIndex memory address = .ok index ↔
    ValidAddress memory address ∧ index = address.toNat / 4 := by
  by_cases ha : address.toNat % 4 = 0 <;>
    by_cases hb : address.toNat / 4 < memory.length <;>
    simp [addressIndex, ValidAddress, ha, hb, eq_comm]

/-- Execute one fetched instruction. `readOverride` is a candidate value for this
step's load; `none` selects the concrete current arena value. Both modes check bounds. -/
def eval (readOverride : Option Word) (instruction : Instr) (s : State) : StepResult :=
  match instruction.op with
  | .unsupported spelling => .unsupported spelling
  | _ =>
      if instruction.guard.eval s then
        let advance := {s with pc := s.pc + 1}
        let event := occurrence s instruction true
        match instruction.op with
        | .mov32 destination source =>
            .next {advance with regs := update s.regs destination (source.eval s)} event
        | .bin32 operation destination left right =>
            .next {advance with regs := update s.regs destination (operation.eval (left.eval s) (right.eval s))} event
        | .unary32 operation destination source =>
            .next {advance with regs := update s.regs destination (operation.eval (source.eval s))} event
        | .mov64 destination source =>
            .next {advance with addrs := update s.addrs destination (source.eval s)} event
        | .add64 destination left right =>
            .next {advance with addrs := update s.addrs destination (left.eval s + right.eval s)} event
        | .cvt64 destination source =>
            .next {advance with addrs := update s.addrs destination (BitVec.ofNat 64 (source.eval s).toNat)} event
        | .setp comparison destination left right =>
            .next {advance with preds := update s.preds destination (comparison.eval (left.eval s) (right.eval s))} event
        | .load destination address =>
            let pointer := address.eval s
            match addressIndex s.memory pointer with
            | .error reason => .fault reason
            | .ok index =>
                let value := readOverride.getD (s.memory[index]!)
                .next {advance with regs := update s.regs destination value}
                  (occurrence s instruction true (some ⟨.load, pointer, value⟩))
        | .store address source =>
            let pointer := address.eval s
            match addressIndex s.memory pointer with
            | .error reason => .fault reason
            | .ok index =>
                let value := source.eval s
                .next {advance with memory := s.memory.set index value}
                  (occurrence s instruction true (some ⟨.store, pointer, value⟩))
        | .bra target => .next {s with pc := target} event
        | .exit => .halted s event
        | .unsupported spelling => .unsupported spelling
      else .next {s with pc := s.pc + 1} (occurrence s instruction false)

def stepWith (readOverride : Option Word) (program : List Instr) (s : State) : StepResult :=
  match program[s.pc]? with
  | none => .fault (.invalidPC s.pc)
  | some instruction => eval readOverride instruction s

def step (program : List Instr) (s : State) : StepResult := stepWith none program s

inductive Stop where
  | exhausted
  | halted
  | fault (reason : Fault)
  | unsupported (spelling : String)
  deriving DecidableEq, Repr

structure RunResult where
  state : State
  status : Stop
  trace : List Occurrence

/-- Fuel counts dispatches, including predicate-false instructions and explicit exit.
A branch to an invalid PC faults at the next dispatch. Exhaustion is a separate status. -/
def runWith : Nat → (Nat → Option Word) → List Instr → State → RunResult
  | 0, _, _, s => ⟨s, .exhausted, []⟩
  | fuel + 1, oracle, program, s =>
      match stepWith (oracle 0) program s with
      | .next next event =>
          let rest := runWith fuel (fun index => oracle (index + 1)) program next
          {rest with trace := event :: rest.trace}
      | .halted final event => ⟨final, .halted, [event]⟩
      | .fault reason => ⟨s, .fault reason, []⟩
      | .unsupported spelling => ⟨s, .unsupported spelling, []⟩

def run (fuel : Nat) (program : List Instr) (s : State) : RunResult :=
  runWith fuel (fun _ => none) program s

/-- The derivation retains the same oracle positions as the executable runner.
Exhaustion is explicit; only `.halted` establishes completion. -/
inductive Runs (program : List Instr) :
    (Nat → Option Word) → State → RunResult → Prop where
  | exhausted : Runs program oracle s ⟨s, .exhausted, []⟩
  | next : stepWith (oracle 0) program s = .next next event →
      Runs program (fun index => oracle (index + 1)) next rest →
      Runs program oracle s {rest with trace := event :: rest.trace}
  | halted : stepWith (oracle 0) program s = .halted final event →
      Runs program oracle s ⟨final, .halted, [event]⟩
  | fault : stepWith (oracle 0) program s = .fault reason →
      Runs program oracle s ⟨s, .fault reason, []⟩
  | unsupported : stepWith (oracle 0) program s = .unsupported spelling →
      Runs program oracle s ⟨s, .unsupported spelling, []⟩

theorem runWith_sound (fuel : Nat) (oracle : Nat → Option Word) (program : List Instr) (s : State) :
    Runs program oracle s (runWith fuel oracle program s) := by
  induction fuel generalizing oracle s with
  | zero => exact .exhausted
  | succ fuel ih =>
      simp only [runWith]
      split
      · exact .next (by assumption) (ih _ _)
      · exact .halted (by assumption)
      · exact .fault (by assumption)
      · exact .unsupported (by assumption)

theorem run_sound (fuel : Nat) (program : List Instr) (s : State) :
    Runs program (fun _ => none) s (run fuel program s) := runWith_sound _ _ _ _

theorem runWith_trace_length (fuel : Nat) (oracle : Nat → Option Word)
    (program : List Instr) (s : State) :
    (runWith fuel oracle program s).trace.length ≤ fuel := by
  induction fuel generalizing oracle s with
  | zero => simp [runWith]
  | succ fuel ih =>
      simp only [runWith]
      split
      · simpa using Nat.succ_le_succ (ih _ _)
      · simp
      · simp
      · simp

/-- Resume only a fuel-exhausted prefix; terminal and error outcomes remain terminal. -/
def resume (fuel : Nat) (program : List Instr) (prior : RunResult) : RunResult :=
  if prior.status = .exhausted then
    let suffix := run fuel program prior.state
    {suffix with trace := prior.trace ++ suffix.trace}
  else prior

theorem run_zero (program : List Instr) (s : State) : run 0 program s = ⟨s, .exhausted, []⟩ := rfl

/-- A false predicate skips a supported operation. Unknown instructions are
rejected before predication, because their predication legality is not established. -/
theorem eval_skipped (h : instruction.guard.eval s = false)
    (supported : ∀ spelling, instruction.op ≠ .unsupported spelling) :
    eval override instruction s =
      .next {s with pc := s.pc + 1} (occurrence s instruction false) := by
  cases hop : instruction.op <;> simp [eval, hop, h]
  exact False.elim (supported _ hop)

theorem shift_left_clamped (value count : Word) (h : 32 ≤ count.toNat) :
    BinOp.eval .shl value count = 0 := by simp [BinOp.eval, Nat.not_lt.mpr h]

theorem shift_right_clamped (value count : Word) (h : 32 ≤ count.toNat) :
    BinOp.eval .shr value count = 0 := by simp [BinOp.eval, Nat.not_lt.mpr h]

theorem unary_exec (s : State) (operation : UnaryOp) (destination : Nat)
    (source : Operand32) (guard : Guard) (h : guard.eval s = true)
    (readOverride : Option Word) :
    eval readOverride ⟨guard, .unary32 operation destination source⟩ s =
      .next {({s with pc := s.pc + 1}) with
        regs := update s.regs destination (operation.eval (source.eval s))}
        (occurrence s ⟨guard, .unary32 operation destination source⟩ true) := by
  simp [eval, h]

theorem unary_false (s : State) (operation : UnaryOp) (destination : Nat)
    (source : Operand32) (guard : Guard) (h : guard.eval s = false)
    (readOverride : Option Word) :
    eval readOverride ⟨guard, .unary32 operation destination source⟩ s =
      .next {s with pc := s.pc + 1}
        (occurrence s ⟨guard, .unary32 operation destination source⟩ false) := by
  simp [eval, h]

theorem unary_preserves_other (s : State) (operation : UnaryOp) (destination other : Nat)
    (source : Operand32) (guard : Guard) (h : guard.eval s = true)
    (different : other ≠ destination) (readOverride : Option Word) :
    (match eval readOverride ⟨guard, .unary32 operation destination source⟩ s with
      | .next next _ => next.regs other | _ => s.regs other) = s.regs other := by
  rw [unary_exec s operation destination source guard h readOverride]
  simp [update, different]



@[simp] theorem run_succ (fuel : Nat) (program : List Instr) (s : State) :
    run (fuel + 1) program s =
      match step program s with
      | .next next event =>
          let rest := run fuel program next
          {rest with trace := event :: rest.trace}
      | .halted final event => ⟨final, .halted, [event]⟩
      | .fault reason => ⟨s, .fault reason, []⟩
      | .unsupported spelling => ⟨s, .unsupported spelling, []⟩ := rfl

/-- Splitting a budget preserves exact states, outcomes, and complete dynamic traces. -/
theorem run_add (first second : Nat) (program : List Instr) (s : State) :
    run (first + second) program s = resume second program (run first program s) := by
  induction first generalizing s with
  | zero => simp [run_zero, resume]
  | succ first ih =>
      rw [Nat.succ_add, run_succ, run_succ]
      cases hs : step program s with
      | next next event =>
          simp only
          rw [ih]
          simp [resume]
          split <;> rfl
      | halted final event => simp [resume]
      | fault reason => simp [resume]
      | unsupported spelling => simp [resume]

/-- Every successful memory effect has passed alignment and arena-bounds checks,
including effects from candidate loads whose values were overridden. -/
theorem eval_memory_safe
    (hstep : eval override instruction s = .next next event)
    (hmemory : event.memory = some effect) : ValidAddress s.memory effect.address := by
  cases instruction with
  | mk guard op =>
    cases op <;> cases hguard : guard.eval s <;>
      simp only [eval, hguard, ↓reduceIte] at hstep
    all_goals first
      | (obtain ⟨_, rfl⟩ := StepResult.next.inj hstep; simp [occurrence] at hmemory)
      | contradiction
      | skip
    all_goals
      split at hstep
      · contradiction
      · obtain ⟨_, rfl⟩ := StepResult.next.inj hstep
        simp only [occurrence, Option.some.injEq] at hmemory
        subst effect
        exact (addressIndex_ok_iff.mp (by assumption)).1

/-- Store replacement cannot resize the arena. -/
theorem eval_memory_length (hstep : eval override instruction s = .next next event) :
    next.memory.length = s.memory.length := by
  cases instruction with
  | mk guard op =>
    cases op <;> cases hguard : guard.eval s <;>
      simp only [eval, hguard, ↓reduceIte] at hstep
    all_goals first
      | (obtain ⟨rfl, _⟩ := StepResult.next.inj hstep; simp)
      | contradiction
      | skip
    all_goals
      split at hstep
      · contradiction
      · obtain ⟨rfl, _⟩ := StepResult.next.inj hstep
        simp

theorem step_memory_safe
    (hstep : stepWith override program s = .next next event)
    (hmemory : event.memory = some effect) : ValidAddress s.memory effect.address := by
  unfold stepWith at hstep
  split at hstep
  · contradiction
  · exact eval_memory_safe hstep hmemory

theorem step_memory_length (hstep : stepWith override program s = .next next event) :
    next.memory.length = s.memory.length := by
  unfold stepWith at hstep
  split at hstep
  · contradiction
  · exact eval_memory_length hstep



/-- Only explicit exit halts, and it does not change state or access memory. -/
theorem eval_halted (hstep : eval override instruction s = .halted final event) :
    final = s ∧ event.memory = none := by
  cases instruction with
  | mk guard op =>
    cases op <;> cases hguard : guard.eval s <;>
      simp only [eval, hguard, ↓reduceIte] at hstep
    all_goals first
      | (obtain ⟨rfl, rfl⟩ := StepResult.halted.inj hstep; exact ⟨rfl, rfl⟩)
      | contradiction
      | skip
    all_goals split at hstep <;> contradiction

theorem step_halted (hstep : stepWith override program s = .halted final event) :
    final = s ∧ event.memory = none := by
  unfold stepWith at hstep
  split at hstep
  · contradiction
  · exact eval_halted hstep

theorem runWith_memory_length (fuel : Nat) (oracle : Nat → Option Word)
    (program : List Instr) (s : State) :
    (runWith fuel oracle program s).state.memory.length = s.memory.length := by
  induction fuel generalizing oracle s with
  | zero => rfl
  | succ fuel ih =>
      cases hs : stepWith (oracle 0) program s with
      | next next event =>
          simp only [runWith, hs]
          exact (ih _ _).trans (step_memory_length hs)
      | halted final event =>
          simp only [runWith, hs]
          rw [(step_halted hs).1]
      | fault reason => simp [runWith, hs]
      | unsupported spelling => simp [runWith, hs]

theorem run_memory_length (fuel : Nat) (program : List Instr) (s : State) :
    (run fuel program s).state.memory.length = s.memory.length := runWith_memory_length _ _ _ _

/-- Every emitted load/store is safe relative to the initial arena extent, even
if the run later faults, is unsupported, exhausts its budget, or uses candidate reads. -/
theorem runWith_trace_safe (fuel : Nat) (oracle : Nat → Option Word)
    (program : List Instr) (s : State) :
    ∀ event ∈ (runWith fuel oracle program s).trace,
      ∀ effect, event.memory = some effect → ValidAddress s.memory effect.address := by
  induction fuel generalizing oracle s with
  | zero => simp [runWith]
  | succ fuel ih =>
      cases hs : stepWith (oracle 0) program s with
      | next next emitted =>
          simp only [runWith, hs, List.mem_cons]
          intro event member effect memory
          rcases member with rfl | member
          · exact step_memory_safe hs memory
          · have safe := ih _ next event member effect memory
            simpa only [ValidAddress, step_memory_length hs] using safe
      | halted final emitted =>
          simp only [runWith, hs, List.mem_singleton]
          intro event member effect memory
          subst event
          rw [(step_halted hs).2] at memory
          contradiction
      | fault reason => simp [runWith, hs]
      | unsupported spelling => simp [runWith, hs]

theorem run_trace_safe (fuel : Nat) (program : List Instr) (s : State) :
    ∀ event ∈ (run fuel program s).trace,
      ∀ effect, event.memory = some effect → ValidAddress s.memory effect.address :=
  runWith_trace_safe _ _ _ _

/-- The inductive run relation has no extra executions beyond some finite budget
of the executable semantics. This includes explicitly incomplete prefixes. -/
theorem Runs.exists_run (h : Runs program oracle s result) :
    ∃ fuel, runWith fuel oracle program s = result := by
  induction h with
  | exhausted => exact ⟨0, rfl⟩
  | @next oracle s next event rest hs hr ih =>
      obtain ⟨fuel, hf⟩ := ih
      exact ⟨fuel + 1, by simp [runWith, hs, hf]⟩
  | halted hs => exact ⟨1, by simp [runWith, hs]⟩
  | fault hs => exact ⟨1, by simp [runWith, hs]⟩
  | unsupported hs => exact ⟨1, by simp [runWith, hs]⟩



/-- Unsaturated fixed-width integer operations expose their exact modular meaning. -/
theorem add_modulo (a b : Word) :
    (BinOp.eval .add a b).toNat = (a.toNat + b.toNat) % 2 ^ 32 := rfl

theorem sub_modulo (a b : Word) :
    (BinOp.eval .sub a b).toNat = ((2 ^ 32 - b.toNat) + a.toNat) % 2 ^ 32 := rfl

theorem mul_low_modulo (a b : Word) :
    (BinOp.eval .mulLo a b).toNat = (a.toNat * b.toNat) % 2 ^ 32 := rfl

/-- The address register operation wraps at 64 bits rather than growing in Nat. -/
theorem add64_modulo (a b : Address) :
    (a + b).toNat = (a.toNat + b.toNat) % 2 ^ 64 := rfl

/-- Validity covers the entire four-byte access, not just its first byte. -/
theorem validAddress_bytes (h : ValidAddress memory address) :
    address.toNat % 4 = 0 ∧ address.toNat + 4 ≤ 4 * memory.length := by
  obtain ⟨aligned, bounded⟩ := h
  have division := Nat.mod_add_div address.toNat 4
  exact ⟨aligned, by omega⟩

theorem unsupported_not_hidden (s : State) (guard : Guard) (spelling : String) :
    eval override ⟨guard, .unsupported spelling⟩ s = .unsupported spelling := rfl

/-- Shift counts at and beyond the width cannot be accidentally masked modulo 32. -/
theorem shift_boundary_examples :
    BinOp.eval .shl 1 31 = 2147483648 ∧
    BinOp.eval .shl 1 32 = 0 ∧ BinOp.eval .shl 1 33 = 0 ∧
    BinOp.eval .shr 4294967295 32 = 0 := by decide

theorem unsigned_wrap_examples :
    BinOp.eval .add 4294967295 1 = 0 ∧
    BinOp.eval .sub 0 1 = 4294967295 ∧
    BinOp.eval .mulLo 4294967295 2 = 4294967294 := by decide

end Ptx.Scalar

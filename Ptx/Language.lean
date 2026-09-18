import Std

/-!
# Local execution for the message-passing fragment

This typed, straight-line language has aligned, non-overlapping 32-bit accesses
to a single global-memory arena. Addresses are word indices, not raw pointers.
Stores use immediate operands. Loads receive a candidate value from an oracle;
the global memory model separately decides whether those values are permitted.
There is no branch, address arithmetic, parsing, allocation, or GPU scheduler.
-/

namespace Ptx

abbrev Word := BitVec 32
abbrev Registers := Nat → Word

inductive LoadOrder where
  | relaxed
  | acquire
  deriving DecidableEq, Repr

inductive StoreOrder where
  | relaxed
  | release
  deriving DecidableEq, Repr

inductive EventOp where
  | load (order : LoadOrder)
  | store (order : StoreOrder)
  | init
  deriving DecidableEq, Repr

structure Effect where
  op : EventOp
  address : Nat
  value : Word
  deriving DecidableEq, Repr

inductive Instr where
  | load (order : LoadOrder) (address destination : Nat)
  | store (order : StoreOrder) (address : Nat) (value : Word)
  deriving DecidableEq, Repr

def Instr.address : Instr → Nat
  | .load _ address _ => address
  | .store _ address _ => address

/-- The memory event requested by an instruction, before global validation. -/
def Instr.effect (instruction : Instr) (readValue : Word) : Effect :=
  match instruction with
  | .load order address _ => ⟨.load order, address, readValue⟩
  | .store order address value => ⟨.store order, address, value⟩

/-- One local instruction. Only loads consume the candidate read value. -/
def Instr.step (instruction : Instr) (registers : Registers) (readValue : Word) :
    Registers × Effect :=
  match instruction with
  | .load order address destination =>
      (fun register => if register = destination then readValue else registers register,
       ⟨.load order, address, readValue⟩)
  | .store order address value =>
      (registers, ⟨.store order, address, value⟩)

/-- A local transition is precisely the graph of the instruction operation. -/
def Step (instruction : Instr) (registers : Registers) (readValue : Word)
    (next : Registers) (effect : Effect) : Prop :=
  instruction.step registers readValue = (next, effect)

theorem step_exists (instruction : Instr) (registers : Registers) (readValue : Word) :
    ∃ next effect, Step instruction registers readValue next effect := by
  exact ⟨(instruction.step registers readValue).1,
    (instruction.step registers readValue).2, rfl⟩

theorem step_deterministic
    (h₁ : Step instruction registers readValue next₁ effect₁)
    (h₂ : Step instruction registers readValue next₂ effect₂) :
    next₁ = next₂ ∧ effect₁ = effect₂ := by
  have h : (next₁, effect₁) = (next₂, effect₂) := h₁.symm.trans h₂
  exact Prod.mk.inj h

@[simp] theorem step_address (instruction : Instr) (registers : Registers)
    (readValue : Word) :
    (instruction.step registers readValue).2.address = instruction.address := by
  cases instruction <;> rfl

@[simp] theorem step_effect (instruction : Instr) (registers : Registers) (readValue : Word) :
    (instruction.step registers readValue).2 = instruction.effect readValue := by
  cases instruction <;> rfl

@[simp] theorem load_writes_destination (order : LoadOrder) (address destination : Nat)
    (registers : Registers) (readValue : Word) :
    ((Instr.load order address destination).step registers readValue).1 destination =
      readValue := by
  simp [Instr.step]

theorem load_preserves_other_register (order : LoadOrder) (address destination register : Nat)
    (registers : Registers) (readValue : Word) (h : register ≠ destination) :
    ((Instr.load order address destination).step registers readValue).1 register =
      registers register := by
  simp [Instr.step, h]

@[simp] theorem store_emits_operand (order : StoreOrder) (address : Nat) (value : Word)
    (registers : Registers) (readValue : Word) :
    ((Instr.store order address value).step registers readValue).2 =
      ⟨.store order, address, value⟩ := rfl

@[simp] theorem store_preserves_registers (order : StoreOrder) (address : Nat) (value : Word)
    (registers : Registers) (readValue : Word) :
    ((Instr.store order address value).step registers readValue).1 = registers := rfl

/-- Oracle position is instruction position; values at store positions are ignored. -/
def execute : List Instr → Registers → (Nat → Word) → Registers × List Effect
  | [], registers, _ => (registers, [])
  | instruction :: rest, registers, oracle =>
      let (next, effect) := instruction.step registers (oracle 0)
      let (final, effects) := execute rest next (fun i => oracle (i + 1))
      (final, effect :: effects)

/-- Finite local executions compose instruction transitions in program order. -/
inductive Runs : List Instr → Registers → (Nat → Word) → Registers → List Effect → Prop
  | nil (registers : Registers) (oracle : Nat → Word) :
      Runs [] registers oracle registers []
  | cons : Step instruction registers (oracle 0) next effect →
      Runs rest next (fun i => oracle (i + 1)) final effects →
      Runs (instruction :: rest) registers oracle final (effect :: effects)

theorem execute_runs (program : List Instr) (registers : Registers) (oracle : Nat → Word) :
    Runs program registers oracle (execute program registers oracle).1
      (execute program registers oracle).2 := by
  induction program generalizing registers oracle with
  | nil => exact .nil registers oracle
  | cons instruction rest ih =>
      exact .cons rfl (ih _ _)

theorem runs_eq_execute
    (h : Runs program registers oracle final effects) :
    execute program registers oracle = (final, effects) := by
  induction h with
  | nil => rfl
  | @cons instruction registers oracle next effect rest final effects hs hr ih =>
      simp only [execute, Step] at *
      rw [hs]
      simp only [ih]

theorem runs_exists (program : List Instr) (registers : Registers) (oracle : Nat → Word) :
    ∃ final effects, Runs program registers oracle final effects :=
  ⟨_, _, execute_runs program registers oracle⟩

theorem runs_deterministic
    (h₁ : Runs program registers oracle final₁ effects₁)
    (h₂ : Runs program registers oracle final₂ effects₂) :
    final₁ = final₂ ∧ effects₁ = effects₂ := by
  exact Prod.mk.inj ((runs_eq_execute h₁).symm.trans (runs_eq_execute h₂))

theorem execute_addresses (program : List Instr) (registers : Registers) (oracle : Nat → Word) :
    ((execute program registers oracle).2.map Effect.address) = program.map Instr.address := by
  induction program generalizing registers oracle with
  | nil => rfl
  | cons instruction rest ih =>
      simp only [execute, List.map_cons, step_address, ih]

/-- Every instruction emits exactly one event, in instruction order. -/
theorem execute_effects (program : List Instr) (registers : Registers) (oracle : Nat → Word) :
    (execute program registers oracle).2 =
      program.mapIdx (fun i instruction => instruction.effect (oracle i)) := by
  induction program generalizing registers oracle with
  | nil => simp [execute]
  | cons instruction rest ih =>
      simp only [execute, step_effect, List.mapIdx_cons, ih]

@[simp] theorem execute_length (program : List Instr) (registers : Registers)
    (oracle : Nat → Word) :
    (execute program registers oracle).2.length = program.length := by
  rw [execute_effects]
  simp

theorem execute_getElem? (program : List Instr) (registers : Registers)
    (oracle : Nat → Word) (index : Nat) :
    (execute program registers oracle).2[index]? =
      program[index]?.map (fun instruction => instruction.effect (oracle index)) := by
  rw [execute_effects]
  simp

/-- Byte addresses are mathematical naturals; no finite-pointer arithmetic is modeled. -/
def byteAddress (wordIndex : Nat) : Nat := 4 * wordIndex

def AccessSafe (nWords : Nat) (effect : Effect) : Prop :=
  byteAddress effect.address % 4 = 0 ∧
    byteAddress effect.address + 4 ≤ 4 * nWords

theorem access_safe_of_index_lt (effect : Effect) (h : effect.address < nWords) :
    AccessSafe nWords effect := by
  constructor
  · simp [byteAddress]
  · simp only [byteAddress]
    omega

/-- Arena bounds on typed instructions imply alignment and bounds for all emitted accesses. -/
theorem execute_access_safe (program : List Instr) (registers : Registers) (oracle : Nat → Word)
    (bounded : ∀ instruction ∈ program, instruction.address < nWords) :
    ∀ effect ∈ (execute program registers oracle).2, AccessSafe nWords effect := by
  intro effect he
  apply access_safe_of_index_lt
  have ha : effect.address ∈ (execute program registers oracle).2.map Effect.address :=
    List.mem_map.mpr ⟨effect, he, rfl⟩
  rw [execute_addresses] at ha
  obtain ⟨instruction, hi, haddr⟩ := List.mem_map.mp ha
  rw [← haddr]
  exact bounded instruction hi

def InWordFootprint (wordIndex byte : Nat) : Prop :=
  ∃ offset, offset < 4 ∧ byte = byteAddress wordIndex + offset

/-- Distinct word indices name disjoint complete four-byte footprints. -/
theorem word_footprints_disjoint (different : left ≠ right)
    (hl : InWordFootprint left byte) (hr : InWordFootprint right byte) : False := by
  obtain ⟨lo, hlo, heql⟩ := hl
  obtain ⟨ro, hro, heqr⟩ := hr
  simp only [byteAddress] at *
  omega

end Ptx

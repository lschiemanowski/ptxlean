import PoissonPTX.Bytes
import FloatLib.Floats.Formats.IEEE754.Native.Representation

/-! Fetched straight-line binary64 PTX instructions with real byte-addressed
loads/stores. This module does not give weak-memory admission or barrier rules. -/
namespace PtxTorchLean.Poisson.PTX
open FloatLib.Floats.ExecFloat

abbrev Registers := Nat → Word

def decode (w : Word) : Float := Float.ofBits (UInt64.ofBitVec w)
def encode (x : Float) : Word := x.toBits.toBitVec

@[simp] theorem decode_encode (x : Float) : decode (encode x) = x := by
  exact Binary.toFloat_ofFloat x

inductive FP where
  | add | sub | mul | div
  deriving DecidableEq, Repr

def FP.apply : FP → Float → Float → Float
  | .add, a, b => a+b
  | .sub, a, b => a-b
  | .mul, a, b => a*b
  | .div, a, b => a/b

/-- Equality after canonical NaN decoding preserves freedom in NaN payloads.
It is a primitive arithmetic contract, not a desired kernel-output premise. -/
def FP.Result (op : FP) (a b out : Word) : Prop :=
  decode out = op.apply (decode a) (decode b)

instance (op : FP) (a b out : Word) : Decidable (op.Result a b out) :=
  inferInstanceAs (Decidable (decode out = op.apply (decode a) (decode b)))

theorem FP.result_exists (op : FP) (a b : Word) : ∃ out, op.Result a b out :=
  ⟨encode (op.apply (decode a) (decode b)), decode_encode _⟩

inductive Space where
  | global | shared
  deriving DecidableEq, Repr

structure State where
  pc : Nat
  regs : Registers
  global : Memory
  shared : Memory
  globalStart : Nat
  globalBytes : Nat
  sharedStart : Nat
  sharedBytes : Nat

inductive Operand where
  | reg (index : Nat)
  | imm (value : Word)
  deriving DecidableEq, Repr

def Operand.eval (s : State) : Operand → Word
  | .reg r => s.regs r
  | .imm w => w

inductive Op where
  | mov (dst : Nat) (src : Operand)
  | add64 (dst : Nat) (a b : Operand)
  | wide8 (dst : Nat) (index : Operand)
  | load64 (space : Space) (dst : Nat) (address : Operand)
  | store64 (space : Space) (address src : Operand)
  | fp (op : FP) (dst : Nat) (a b : Operand)
  deriving DecidableEq, Repr

def State.memory (s : State) : Space → Memory
  | .global => s.global
  | .shared => s.shared

def State.start (s : State) : Space → Nat
  | .global => s.globalStart
  | .shared => s.sharedStart

def State.bytes (s : State) : Space → Nat
  | .global => s.globalBytes
  | .shared => s.sharedBytes

def advance (s : State) : State := {s with pc := s.pc+1}
def assign (s : State) (r : Nat) (w : Word) : State :=
  {advance s with regs := Function.update s.regs r w}

def put (s : State) (space : Space) (address : Nat) (value : Word) : State :=
  match space with
  | .global => {advance s with global := write64 s.global address value}
  | .shared => {advance s with shared := write64 s.shared address value}

/-- Actual instruction execution. Invalid byte accesses have no successful
step; the checked interpreter below returns none instead of inventing a value. -/
inductive Eval : Op → State → State → Prop where
  | mov : Eval (.mov dst src) s (assign s dst (src.eval s))
  | add64 : Eval (.add64 dst a b) s (assign s dst (a.eval s+b.eval s))
  | wide8 : Eval (.wide8 dst index) s (assign s dst (BitVec.ofNat 64 ((index.eval s).toNat % 2^32 * 8)))
  | load64 (valid : Valid64 (s.start space) (s.bytes space) (address.eval s).toNat) :
      Eval (.load64 space dst address) s
        (assign s dst (read64 (s.memory space) (address.eval s).toNat))
  | store64 (valid : Valid64 (s.start space) (s.bytes space) (address.eval s).toNat) :
      Eval (.store64 space address src) s
        (put s space (address.eval s).toNat (src.eval s))
  | fp (allowed : op.Result (a.eval s) (b.eval s) out) :
      Eval (.fp op dst a b) s (assign s dst out)

def Step (program : List Op) (s t : State) : Prop :=
  ∃ op, program[s.pc]? = some op ∧ Eval op s t

inductive Runs (program : List Op) : State → State → Prop where
  | nil : Runs program s s
  | cons : Step program s t → Runs program t u → Runs program s u

/-- Sequential code-block execution. A theorem below embeds it into fetched
program execution at the exact block offset. -/
inductive Block : List Op → State → State → Prop where
  | nil : Block [] s s
  | cons : Eval op s t → Block ops t u → Block (op::ops) s u

theorem eval_pc (h : Eval op s t) : t.pc = s.pc+1 := by
  cases h <;> try rfl
  case store64 => cases ‹Space› <;> rfl

theorem block_pc (h : Block code s t) : t.pc = s.pc+code.length := by
  induction h with
  | nil => simp
  | cons he _ ih => rw [ih,eval_pc he]; simp only [List.length_cons]; omega

theorem block_append (a : Block left s t) (b : Block right t u) :
    Block (left++right) s u := by
  induction a with
  | nil => exact b
  | cons he _ ih => exact .cons he (ih b)

/-- Every step fetches the actual instruction; there is no supplied trace-label
assumption. A block may occur inside a larger program. -/
theorem block_fetched (h : Block code s t) (precode suffix : List Op)
    (pc : s.pc = precode.length) : Runs (precode++code++suffix) s t := by
  induction h generalizing precode with
  | nil => exact .nil
  | @cons op s middle ops t he hb ih =>
    have fetch : (precode++(op::ops)++suffix)[s.pc]? = some op := by simp [pc]
    apply Runs.cons ⟨op,fetch,he⟩
    have hm : middle.pc = (precode++[op]).length := by simp [eval_pc he,pc]
    simpa [List.append_assoc] using ih (precode++[op]) hm

/-- Executable canonical witness; relational Eval still allows other NaN bits. -/
def eval (op : Op) (s : State) : Option State :=
  match op with
  | .mov dst src => some (assign s dst (src.eval s))
  | .add64 dst a b => some (assign s dst (a.eval s+b.eval s))
  | .wide8 dst i => some (assign s dst (BitVec.ofNat 64 ((i.eval s).toNat % 2^32 * 8)))
  | .load64 space dst address =>
      if Valid64 (s.start space) (s.bytes space) (address.eval s).toNat then
        some (assign s dst (read64 (s.memory space) (address.eval s).toNat)) else none
  | .store64 space address src =>
      if Valid64 (s.start space) (s.bytes space) (address.eval s).toNat then
        some (put s space (address.eval s).toNat (src.eval s)) else none
  | .fp op dst a b => some (assign s dst (encode (op.apply (decode (a.eval s)) (decode (b.eval s)))))

def run : List Op → State → Option State
  | [],s => some s
  | op::ops,s => eval op s >>= run ops

theorem eval_sound (h : eval op s = some t) : Eval op s t := by
  cases op <;> simp only [eval] at h
  case mov => cases h; exact .mov
  case add64 => cases h; exact .add64
  case wide8 => cases h; exact .wide8
  case load64 => split at h <;> simp_all; subst t; exact .load64 (by assumption)
  case store64 => split at h <;> simp_all; subst t; exact .store64 (by assumption)
  case fp => cases h; exact .fp (decode_encode _)

theorem run_sound (h : run code s = some t) : Block code s t := by
  induction code generalizing s with
  | nil => simp [run] at h; subst t; exact .nil
  | cons op ops ih =>
    simp only [run] at h
    cases he : eval op s with
    | none => simp [he] at h
    | some middle => exact .cons (eval_sound he) (ih (by simpa [he] using h))

/-- Non-arithmetic instructions have no NaN-result choice. -/
def noFP : Op → Bool
  | .fp .. => false
  | _ => true

theorem eval_complete (h : Eval op s t) (hn : noFP op = true) : eval op s = some t := by
  cases h <;> simp_all [noFP,eval]

theorem block_complete (h : Block code s t)
    (hn : ∀ op ∈ code, noFP op = true) : run code s = some t := by
  induction h with
  | nil => rfl
  | cons he hb ih =>
    simp only [run,eval_complete he (hn _ (by simp)),Option.bind_some]
    exact ih (fun op hop => hn op (by simp [hop]))

theorem block_split (left right : List Op) (h : Block (left++right) s t) :
    ∃ middle, Block left s middle ∧ Block right middle t := by
  induction left generalizing s with
  | nil => exact ⟨s,.nil,h⟩
  | cons op ops ih =>
    cases h with
    | cons he hb =>
      obtain ⟨middle,hleft,hright⟩ := ih hb
      exact ⟨middle,.cons he hleft,hright⟩

end PtxTorchLean.Poisson.PTX

import Ptx.Scalar

/-!
# Typed mnemonic boundary

This decoder consumes a mnemonic and already-tokenized, typed operands. It is not
a raw PTX lexer/parser, module parser, register-declaration checker, or label
resolver. `label` carries a resolved instruction index. Canonical encoding has a
checked round trip for every supported instruction, including its predicate.
-/
namespace Ptx.Scalar.Text

inductive Token where
  | word (operand : Operand32)
  | address (operand : Operand64)
  | predicate (index : Nat)
  | memory (address : Operand64)
  | label (resolvedPC : Nat)
  deriving DecidableEq, Repr

structure Statement where
  guard : Guard := .always
  mnemonic : String
  operands : List Token
  deriving DecidableEq, Repr

inductive DecodeError where
  | unsupportedMnemonic (mnemonic : String)
  | invalidOperands (mnemonic : String)
  deriving DecidableEq, Repr

def binMnemonic : BinOp → String
  | .add => "add.u32"
  | .sub => "sub.u32"
  | .mulLo => "mul.lo.u32"
  | .and => "and.b32"
  | .or => "or.b32"
  | .xor => "xor.b32"
  | .shl => "shl.b32"
  | .shr => "shr.u32"

def compareMnemonic : Compare → String
  | .eq => "setp.eq.u32"
  | .ne => "setp.ne.u32"
  | .lt => "setp.lt.u32"
  | .le => "setp.le.u32"
  | .gt => "setp.gt.u32"
  | .ge => "setp.ge.u32"

def supportedMnemonic (mnemonic : String) : Bool :=
  mnemonic ∈ ["mov.b32", "add.u32", "sub.u32", "mul.lo.u32", "and.b32", "or.b32", "xor.b32",
    "shl.b32", "shr.u32", "mov.b64", "add.u64", "cvt.u64.u32", "setp.eq.u32", "setp.ne.u32",
    "setp.lt.u32", "setp.le.u32", "setp.gt.u32", "setp.ge.u32",
    "ld.relaxed.gpu.global.u32", "st.relaxed.gpu.global.u32", "bra", "exit"]

def decodeOp (mnemonic : String) (operands : List Token) : Except DecodeError Op :=
  match mnemonic, operands with
  | "mov.b32", [.word (.reg d), .word s] => .ok (.mov32 d s)
  | "add.u32", [.word (.reg d), .word a, .word b] => .ok (.bin32 .add d a b)
  | "sub.u32", [.word (.reg d), .word a, .word b] => .ok (.bin32 .sub d a b)
  | "mul.lo.u32", [.word (.reg d), .word a, .word b] => .ok (.bin32 .mulLo d a b)
  | "and.b32", [.word (.reg d), .word a, .word b] => .ok (.bin32 .and d a b)
  | "or.b32", [.word (.reg d), .word a, .word b] => .ok (.bin32 .or d a b)
  | "xor.b32", [.word (.reg d), .word a, .word b] => .ok (.bin32 .xor d a b)
  | "shl.b32", [.word (.reg d), .word a, .word b] => .ok (.bin32 .shl d a b)
  | "shr.u32", [.word (.reg d), .word a, .word b] => .ok (.bin32 .shr d a b)
  | "mov.b64", [.address (.reg d), .address s] => .ok (.mov64 d s)
  | "add.u64", [.address (.reg d), .address a, .address b] => .ok (.add64 d a b)
  | "cvt.u64.u32", [.address (.reg d), .word s] => .ok (.cvt64 d s)
  | "setp.eq.u32", [.predicate d, .word a, .word b] => .ok (.setp .eq d a b)
  | "setp.ne.u32", [.predicate d, .word a, .word b] => .ok (.setp .ne d a b)
  | "setp.lt.u32", [.predicate d, .word a, .word b] => .ok (.setp .lt d a b)
  | "setp.le.u32", [.predicate d, .word a, .word b] => .ok (.setp .le d a b)
  | "setp.gt.u32", [.predicate d, .word a, .word b] => .ok (.setp .gt d a b)
  | "setp.ge.u32", [.predicate d, .word a, .word b] => .ok (.setp .ge d a b)
  | "ld.relaxed.gpu.global.u32", [.word (.reg d), .memory address] => .ok (.load d address)
  | "st.relaxed.gpu.global.u32", [.memory address, .word (.reg source)] => .ok (.store address (.reg source))
  | "bra", [.label target] => .ok (.bra target)
  | "exit", [] => .ok .exit
  | mnemonic, _ => if supportedMnemonic mnemonic then .error (.invalidOperands mnemonic)
      else .error (.unsupportedMnemonic mnemonic)

def decode (statement : Statement) : Except DecodeError Instr :=
  (decodeOp statement.mnemonic statement.operands).map fun op => ⟨statement.guard, op⟩

def encodeOp : Op → String × List Token
  | .mov32 d s => ("mov.b32", [.word (.reg d), .word s])
  | .bin32 operation d a b => (binMnemonic operation, [.word (.reg d), .word a, .word b])
  | .mov64 d s => ("mov.b64", [.address (.reg d), .address s])
  | .add64 d a b => ("add.u64", [.address (.reg d), .address a, .address b])
  | .cvt64 d s => ("cvt.u64.u32", [.address (.reg d), .word s])
  | .setp comparison d a b => (compareMnemonic comparison, [.predicate d, .word a, .word b])
  | .load d address => ("ld.relaxed.gpu.global.u32", [.word (.reg d), .memory address])
  | .store address (.reg source) => ("st.relaxed.gpu.global.u32", [.memory address, .word (.reg source)])
  | .store address (.imm value) => ("internal.store-immediate.u32", [.memory address, .word (.imm value)])
  | .bra target => ("bra", [.label target])
  | .exit => ("exit", [])
  | .unsupported spelling => (spelling, [])

def encode (instruction : Instr) : Statement :=
  ⟨instruction.guard, (encodeOp instruction.op).1, (encodeOp instruction.op).2⟩

/-- Literal stores are an internal machine convenience, not a legal `st` source. -/
def SupportedOp : Op → Prop
  | .unsupported _ | .store _ (.imm _) => False
  | _ => True

def Supported (instruction : Instr) : Prop := SupportedOp instruction.op

theorem decode_encode (instruction : Instr) (supported : Supported instruction) :
    decode (encode instruction) = .ok instruction := by
  rcases instruction with ⟨guard, op⟩
  cases op with
  | bin32 operation d a b => cases operation <;> rfl
  | setp comparison d a b => cases comparison <;> rfl
  | store address source =>
      cases source with
      | reg index => rfl
      | imm value => exact False.elim supported
  | unsupported spelling => exact False.elim supported
  | _ => rfl

/-- Unknown spellings remain explicit errors, including bare weak-memory forms. -/
theorem bare_load_rejected : decodeOp "ld.global.u32" [] =
    .error (.unsupportedMnemonic "ld.global.u32") := rfl

theorem uniform_branch_rejected : decodeOp "bra.uni" [.label 0] =
    .error (.unsupportedMnemonic "bra.uni") := rfl

theorem wrong_destination_rejected : decodeOp "add.u32" [.word (.imm 0), .word (.imm 1), .word (.imm 2)] =
    .error (.invalidOperands "add.u32") := rfl



/-- Decoding cannot manufacture an unsupported operation or an immediate store. -/
theorem decodeOp_supported (h : decodeOp mnemonic operands = .ok op) : SupportedOp op := by
  unfold decodeOp at h
  split at h
  all_goals first
    | (obtain rfl := Except.ok.inj h; trivial)
    | (split at h <;> contradiction)

/-- PTX `st` requires its data operand in the register state space. -/
theorem immediate_store_rejected :
    decodeOp "st.relaxed.gpu.global.u32" [.memory (.reg 0), .word (.imm 7)] =
      .error (.invalidOperands "st.relaxed.gpu.global.u32") := rfl

theorem decode_supported (h : decode statement = .ok instruction) : Supported instruction := by
  unfold decode at h
  cases decoded : decodeOp statement.mnemonic statement.operands with
  | error reason => simp [decoded, Except.map] at h
  | ok op =>
      simp only [decoded, Except.map, Except.ok.injEq] at h
      subst instruction
      exact decodeOp_supported decoded

end Ptx.Scalar.Text

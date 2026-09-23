import Ptx.IntegerBitCount

/-!
Coordinator-owned acceptance checks, frozen before worker dispatch. The basename
uses u32 for the destination; the only supported mnemonics are clz.b32/popc.b32.
The BASELINE section uses only existing APIs. To validate it before a candidate
exists, replace the import by Ptx.ScalarText, truncate at BEGIN CANDIDATE CHECKS,
and append `end Ptx.Scalar.IntegerBitCountAcceptance` in a temporary driver.
This does not implement either instruction. Candidate checks must later compile
unchanged against the real worker outputs in fresh offline replay.
-/
namespace Ptx.Scalar.IntegerBitCountAcceptance

deriving instance DecidableEq for Except
set_option synthInstance.maxSize 4096

-- BEGIN BASELINE-COMPATIBLE CHECKS
private def population (a : Word) : Nat :=
  ((List.range 32).filter (fun i => a.getLsbD i)).length

private def leadingZeros (a : Word) : Nat :=
  ((List.range 32).reverse.takeWhile (fun i => !a.getLsbD i)).length

-- Independent mathematical oracle probes, separate from the candidate evaluator.
example : population 0 = 0 ∧ leadingZeros 0 = 32 := by decide
example : population 1 = 1 ∧ leadingZeros 1 = 31 := by decide
example : population 0x80000000 = 1 ∧ leadingZeros 0x80000000 = 0 := by decide
example : population 0xffffffff = 32 ∧ leadingZeros 0xffffffff = 0 := by decide
example : population 0x7fffffff = 31 ∧ leadingZeros 0x7fffffff = 1 := by decide
example : population 0x00f00001 = 5 ∧ leadingZeros 0x00f00001 = 8 := by decide
example : population 0xaaaaaaaa = 16 ∧ leadingZeros 0xaaaaaaaa = 0 := by decide
example : population 0x55555555 = 16 ∧ leadingZeros 0x55555555 = 1 := by decide

private def initial : State :=
  { pc := 9
    regs := fun i => if i = 0 then 0x00f00001 else if i = 1 then 0xffffffff else 99
    addrs := fun _ => 0x1000
    preds := fun i => i = 1
    memory := [3, 5] }

private def observation (result : StepResult) :
    Option (Nat × Word × Word × Word × Address × Bool × List Word × Occurrence) :=
  match result with
  | .next s event => some (s.pc, s.regs 0, s.regs 1, s.regs 2,
      s.addrs 0, s.preds 1, s.memory, event)
  | _ => none

-- The expected trace names the source/destination explicitly, rather than
-- reusing the worker's new Op.reads/Op.writes cases as the expected oracle.
private def expected (instruction : Instr) (executed : Bool)
    (reads writes : List Register) (r0 r1 : Word) :
    Option (Nat × Word × Word × Word × Address × Bool × List Word × Occurrence) :=
  some (10, r0, r1, 99, 0x1000, true, [3, 5],
    ⟨9, instruction, executed, reads, writes, none⟩)

-- Existing operation/typed-interface probes detect accidental changes to old cases.
example : BinOp.eval .minU 0x80000000 7 = 7 ∧ BinOp.eval .maxU 0x80000000 7 = 0x80000000 := by decide
example : Text.decodeOp "add.u32" [.word (.reg 0), .word (.reg 1), .word (.imm 2)] =
    .ok (.bin32 .add 0 (.reg 1) (.imm 2)) := by decide
example : Text.decodeOp "st.relaxed.gpu.global.u32" [.memory (.reg 0), .word (.imm 7)] =
    .error (.invalidOperands "st.relaxed.gpu.global.u32") := by decide

-- BEGIN CANDIDATE CHECKS
-- Exact universal signatures prevent hidden input-domain or desired-output assumptions.
theorem popc_signature : ∀ a : Word,
    (UnaryOp.eval .popc a).toNat = ((List.range 32).filter (fun i => a.getLsbD i)).length :=
  IntegerBitCount.popc_toNat

theorem clz_signature : ∀ a : Word,
    (UnaryOp.eval .clz a).toNat = ((List.range 32).reverse.takeWhile (fun i => !a.getLsbD i)).length :=
  IntegerBitCount.clz_toNat

theorem popc_bound_signature : ∀ a : Word, (UnaryOp.eval .popc a).toNat ≤ 32 :=
  IntegerBitCount.popc_bound

theorem clz_bound_signature : ∀ a : Word, (UnaryOp.eval .clz a).toNat ≤ 32 :=
  IntegerBitCount.clz_bound

theorem popc_zero_signature : ∀ a : Word, UnaryOp.eval .popc a = 0 ↔ a = 0 :=
  IntegerBitCount.popc_zero_iff

theorem clz_width_signature : ∀ a : Word, UnaryOp.eval .clz a = 32 ↔ a = 0 :=
  IntegerBitCount.clz_width_iff

theorem execution_signature (s : State) (operation : UnaryOp) (destination : Nat)
    (source : Operand32) (guard : Guard) (h : guard.eval s = true)
    (readOverride : Option Word) :
    eval readOverride ⟨guard, .unary32 operation destination source⟩ s =
      .next {s with pc := s.pc + 1, regs := update s.regs destination (operation.eval (source.eval s))}
        (occurrence s ⟨guard, .unary32 operation destination source⟩ true) :=
  IntegerBitCount.unary_exec s operation destination source guard h readOverride

theorem skipped_signature (s : State) (operation : UnaryOp) (destination : Nat)
    (source : Operand32) (guard : Guard) (h : guard.eval s = false)
    (readOverride : Option Word) :
    eval readOverride ⟨guard, .unary32 operation destination source⟩ s =
      .next {s with pc := s.pc + 1}
        (occurrence s ⟨guard, .unary32 operation destination source⟩ false) :=
  IntegerBitCount.unary_false s operation destination source guard h readOverride

theorem frame_signature (s : State) (operation : UnaryOp) (destination other : Nat)
    (source : Operand32) (guard : Guard) (h : guard.eval s = true)
    (different : other ≠ destination) (readOverride : Option Word) :
    (match eval readOverride ⟨guard, .unary32 operation destination source⟩ s with
      | .next next _ => next.regs other | _ => s.regs other) = s.regs other :=
  IntegerBitCount.unary_preserves_other s operation destination other source guard h different readOverride

-- Independent exact arithmetic outcomes, without invoking worker theorems.
example : UnaryOp.eval .popc 0 = 0 ∧ UnaryOp.eval .clz 0 = 32 := by first | rfl | decide
example : UnaryOp.eval .popc 1 = 1 ∧ UnaryOp.eval .clz 1 = 31 := by first | rfl | decide
example : UnaryOp.eval .popc 2 = 1 ∧ UnaryOp.eval .clz 2 = 30 := by first | rfl | decide
example : UnaryOp.eval .popc 0x80000000 = 1 ∧ UnaryOp.eval .clz 0x80000000 = 0 := by first | rfl | decide
example : UnaryOp.eval .popc 0xffffffff = 32 ∧ UnaryOp.eval .clz 0xffffffff = 0 := by first | rfl | decide
example : UnaryOp.eval .popc 0x7fffffff = 31 ∧ UnaryOp.eval .clz 0x7fffffff = 1 := by first | rfl | decide
example : UnaryOp.eval .popc 0x00f00001 = 5 ∧ UnaryOp.eval .clz 0x00f00001 = 8 := by first | rfl | decide
example : UnaryOp.eval .popc 0xaaaaaaaa = 16 ∧ UnaryOp.eval .clz 0xaaaaaaaa = 0 := by first | rfl | decide
example : UnaryOp.eval .popc 0x55555555 = 16 ∧ UnaryOp.eval .clz 0x55555555 = 1 := by first | rfl | decide

-- Input/output aliases must consume the incoming value; both results change it.
example : observation (eval none (.plain (.unary32 .clz 0 (.reg 0))) initial) =
    expected (.plain (.unary32 .clz 0 (.reg 0))) true [.word 0] [.word 0] 8 0xffffffff := by first | rfl | decide
example : observation (eval none (.plain (.unary32 .popc 0 (.reg 0))) initial) =
    expected (.plain (.unary32 .popc 0 (.reg 0))) true [.word 0] [.word 0] 5 0xffffffff := by first | rfl | decide

-- False positive and negative guards omit data reads and writes.
example : observation (eval (some 77) ⟨.pred 0 true, .unary32 .clz 0 (.reg 0)⟩ initial) =
    expected ⟨.pred 0 true, .unary32 .clz 0 (.reg 0)⟩ false [.predicate 0] [] 0x00f00001 0xffffffff := by first | rfl | decide
example : observation (eval (some 77) ⟨.pred 1 false, .unary32 .popc 0 (.reg 0)⟩ initial) =
    expected ⟨.pred 1 false, .unary32 .popc 0 (.reg 0)⟩ false [.predicate 1] [] 0x00f00001 0xffffffff := by first | rfl | decide

-- True negative predicate and literal source, with explicit trace metadata.
example : observation (eval (some 77) ⟨.pred 0 false, .unary32 .popc 1 (.imm 0xffffffff)⟩ initial) =
    expected ⟨.pred 0 false, .unary32 .popc 1 (.imm 0xffffffff)⟩ true [.predicate 0] [.word 1] 0x00f00001 32 := by first | rfl | decide

open Text

example : decode ⟨.pred 1 false, "clz.b32", [.word (.reg 0), .word (.reg 1)]⟩ =
    .ok ⟨.pred 1 false, .unary32 .clz 0 (.reg 1)⟩ := by first | rfl | decide
example : decode ⟨.pred 1 false, "clz.b32", [.word (.reg 0), .word (.imm 0x80000000)]⟩ =
    .ok ⟨.pred 1 false, .unary32 .clz 0 (.imm 0x80000000)⟩ := by first | rfl | decide
example : encode ⟨.pred 0 true, .unary32 .clz 0 (.reg 1)⟩ =
    ⟨.pred 0 true, "clz.b32", [.word (.reg 0), .word (.reg 1)]⟩ := by first | rfl | decide
example : decodeOp "clz.b32" [] =
    .error (.invalidOperands "clz.b32") := by first | rfl | decide
example : decodeOp "clz.b32" [.word (.reg 0)] =
    .error (.invalidOperands "clz.b32") := by first | rfl | decide
example : decodeOp "clz.b32" [.word (.reg 0), .word (.reg 1), .word (.imm 1)] =
    .error (.invalidOperands "clz.b32") := by first | rfl | decide
example : decodeOp "clz.b32" [.word (.imm 0), .word (.reg 1)] =
    .error (.invalidOperands "clz.b32") := by first | rfl | decide
example : decodeOp "clz.b32" [.word (.reg 0), .address (.reg 1)] =
    .error (.invalidOperands "clz.b32") := by first | rfl | decide
example : decodeOp "clz.b32" [.predicate 0, .word (.reg 1)] =
    .error (.invalidOperands "clz.b32") := by first | rfl | decide
example : decodeOp "clz.b64" [.word (.reg 0), .word (.reg 1)] =
    .error (.unsupportedMnemonic "clz.b64") := by first | rfl | decide
example : decodeOp "clz.u32" [.word (.reg 0), .word (.reg 1)] =
    .error (.unsupportedMnemonic "clz.u32") := by first | rfl | decide
example : decodeOp "clz.s32" [.word (.reg 0), .word (.reg 1)] =
    .error (.unsupportedMnemonic "clz.s32") := by first | rfl | decide
example : decodeOp "clz.sat.b32" [.word (.reg 0), .word (.reg 1)] =
    .error (.unsupportedMnemonic "clz.sat.b32") := by first | rfl | decide
example : decodeOp "clz.b16" [.word (.reg 0), .word (.reg 1)] =
    .error (.unsupportedMnemonic "clz.b16") := by first | rfl | decide
example : decode ⟨.pred 1 false, "popc.b32", [.word (.reg 0), .word (.reg 1)]⟩ =
    .ok ⟨.pred 1 false, .unary32 .popc 0 (.reg 1)⟩ := by first | rfl | decide
example : decode ⟨.pred 1 false, "popc.b32", [.word (.reg 0), .word (.imm 0x80000000)]⟩ =
    .ok ⟨.pred 1 false, .unary32 .popc 0 (.imm 0x80000000)⟩ := by first | rfl | decide
example : encode ⟨.pred 0 true, .unary32 .popc 0 (.reg 1)⟩ =
    ⟨.pred 0 true, "popc.b32", [.word (.reg 0), .word (.reg 1)]⟩ := by first | rfl | decide
example : decodeOp "popc.b32" [] =
    .error (.invalidOperands "popc.b32") := by first | rfl | decide
example : decodeOp "popc.b32" [.word (.reg 0)] =
    .error (.invalidOperands "popc.b32") := by first | rfl | decide
example : decodeOp "popc.b32" [.word (.reg 0), .word (.reg 1), .word (.imm 1)] =
    .error (.invalidOperands "popc.b32") := by first | rfl | decide
example : decodeOp "popc.b32" [.word (.imm 0), .word (.reg 1)] =
    .error (.invalidOperands "popc.b32") := by first | rfl | decide
example : decodeOp "popc.b32" [.word (.reg 0), .address (.reg 1)] =
    .error (.invalidOperands "popc.b32") := by first | rfl | decide
example : decodeOp "popc.b32" [.predicate 0, .word (.reg 1)] =
    .error (.invalidOperands "popc.b32") := by first | rfl | decide
example : decodeOp "popc.b64" [.word (.reg 0), .word (.reg 1)] =
    .error (.unsupportedMnemonic "popc.b64") := by first | rfl | decide
example : decodeOp "popc.u32" [.word (.reg 0), .word (.reg 1)] =
    .error (.unsupportedMnemonic "popc.u32") := by first | rfl | decide
example : decodeOp "popc.s32" [.word (.reg 0), .word (.reg 1)] =
    .error (.unsupportedMnemonic "popc.s32") := by first | rfl | decide
example : decodeOp "popc.sat.b32" [.word (.reg 0), .word (.reg 1)] =
    .error (.unsupportedMnemonic "popc.sat.b32") := by first | rfl | decide
example : decodeOp "popc.b16" [.word (.reg 0), .word (.reg 1)] =
    .error (.unsupportedMnemonic "popc.b16") := by first | rfl | decide

#print axioms popc_signature
#print axioms clz_signature
#print axioms execution_signature
#print axioms skipped_signature
#print axioms frame_signature
#print axioms Text.decode_encode
#print axioms Text.decodeOp_supported

end Ptx.Scalar.IntegerBitCountAcceptance

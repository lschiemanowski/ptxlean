import Ptx.Bfe32
import Ptx.MulHi32
import Ptx.Brev32
import Ptx.PureKernel
import Ptx.Bitwise32
import Ptx.UnaryBits32
import Ptx.Select32
import Ptx.SignedMinMax32
import Ptx.Shift32

/-! A catalog connects existing leaf semantics without redefining their results. -/
namespace Ptx.Scalar.ReviewedPure

inductive Kind where
  | bitwise | unary | select | signedMinMax | shift | brev | mulHi | bfe
  deriving DecidableEq, Repr

def Operation : Kind → Type
  | .bitwise => Bitwise32.Operation
  | .unary => UnaryBits32.Operation
  | .select => Select32.Operation
  | .signedMinMax => SignedMinMax32.Operation
  | .shift => Shift32.Operation
  | .bfe => Bfe32.Operation
  | .mulHi => MulHi32.Operation
  | .brev => Brev32.Operation

def family : (kind : Kind) → Pure32.Family (Operation kind)
  | .bitwise => Bitwise32.family
  | .unary => UnaryBits32.family
  | .select => Select32.family
  | .signedMinMax => SignedMinMax32.family
  | .shift => Shift32.family
  | .bfe => Bfe32.family
  | .mulHi => MulHi32.family
  | .brev => Brev32.family

def catalog : PureKernel.Catalog Kind := ⟨Operation, family⟩

abbrev Instr := PureKernel.Instr catalog
abbrev Event := PureKernel.Event catalog

def bitwise (i : Bitwise32.Instr) : Instr := .pure .bitwise (Bitwise32.lower i)
def unary (i : UnaryBits32.Instr) : Instr := .pure .unary (UnaryBits32.lower i)
def select (i : Select32.Instr) : Instr := .pure .select (Select32.lower i)
def signedMinMax (i : SignedMinMax32.Instr) : Instr := .pure .signedMinMax (SignedMinMax32.lower i)

def shift (i : Shift32.Instr) : Instr := .pure .shift (Shift32.lower i)

def brev (i : Brev32.Instr) : Instr := .pure .brev (Brev32.lower i)

def mulHi (i : MulHi32.Instr) : Instr := .pure .mulHi (MulHi32.lower i)

def bfe (i : Bfe32.Instr) : Instr := .pure .bfe (Bfe32.lower i)

theorem functional : PureKernel.Functional catalog := by
  intro kind
  cases kind <;> intro op words predicates a b ha hb <;> exact ha.trans hb.symm

def scalarBitwise (i : Bitwise32.Instr) : Scalar.Instr :=
  ⟨i.guard, .bin32 (match i.operation with | .bitAnd => .and | .bitOr => .or | .bitXor => .xor)
    i.destination i.left i.right⟩

theorem bitwise_result_agrees (i : Bitwise32.Instr) (s : State) :
    Bitwise32.result i s =
      BinOp.eval (match i.operation with | .bitAnd => .and | .bitOr => .or | .bitXor => .xor)
        (i.left.eval s) (i.right.eval s) := by
  cases h : i.operation <;> simp [Bitwise32.result, Bitwise32.compute, BinOp.eval, h]

theorem bitwise_scalar_step (h : Bitwise32.Eval i s next event) :
    Scalar.eval none (scalarBitwise i) s =
      .next next (Scalar.occurrence s (scalarBitwise i) (i.guard.eval s)) := by
  cases hg : i.guard.eval s with
  | false =>
    obtain ⟨rfl,rfl⟩ := (Bitwise32.eval_false_iff i s next event hg).mp h
    simp [scalarBitwise, Scalar.eval, hg]
  | true =>
    obtain ⟨rfl,rfl⟩ := (Bitwise32.eval_true_iff i s next event hg).mp h
    simp [scalarBitwise, Scalar.eval, hg, Pure32.write, bitwise_result_agrees]

theorem bitwise_scalar_iff : Bitwise32.Eval i s next event ↔
    Scalar.eval none (scalarBitwise i) s =
      .next next (Scalar.occurrence s (scalarBitwise i) (i.guard.eval s)) ∧
    event = Bitwise32.occurrence s i (i.guard.eval s) := by
  constructor
  · intro h
    exact ⟨bitwise_scalar_step h, Bitwise32.eval_event i s next event h⟩
  · rintro ⟨scalarStep, eventEq⟩
    obtain ⟨next',event',h⟩ := Bitwise32.eval_exists i s
    have same := (Scalar.StepResult.next.inj ((bitwise_scalar_step h).symm.trans scalarStep)).1
    subst next'
    have sameEvent := (Bitwise32.eval_event i s next event' h).trans eventEq.symm
    subst event'
    exact h

theorem bitwise_event_agrees (s : State) (i : Bitwise32.Instr) (executed : Bool) :
    let pure := Bitwise32.occurrence s i executed
    let scalar := Scalar.occurrence s (scalarBitwise i) executed
    pure.pc = scalar.pc ∧ pure.executed = scalar.executed ∧
      pure.reads = scalar.reads ∧ pure.writes = scalar.writes ∧ pure.memory = scalar.memory := by
  cases executed <;>
    simp [Bitwise32.occurrence, Pure32.occurrence, Bitwise32.lower,
      Pure32.Instr.sourceReads, scalarBitwise, Scalar.occurrence, Op.reads, Op.writes,
      Bitwise32.family, Pure32.Family.ofFunction, List.ofFn_succ]

theorem shift_left_agrees (a b : Word) : Shift32.compute .shl a b = BinOp.eval .shl a b := rfl

theorem shift_right_agrees (a b : Word) : Shift32.compute .shrU a b = BinOp.eval .shr a b := rfl

end Ptx.Scalar.ReviewedPure

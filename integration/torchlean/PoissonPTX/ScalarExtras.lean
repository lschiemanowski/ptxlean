import PoissonPTX.ControlFlowSegments

namespace PtxTorchLean.Poisson.PTX.Scalar

/-- Binary64 abs preserves a NaN input word in the pinned PTX 9.4 contract;
for numerical inputs it clears only the sign bit. -/
def absolute (a : Word) : Word := if (decode a).isNaN then a else a &&& 0x7fffffffffffffff

/-- The unmodified f64 maximum ignores a sole NaN and ranks positive zero
above negative zero. Decoded equality leaves a both-NaN result encoding free. -/
def maximum (a b : Word) : Float :=
  if (decode a).isNaN then decode b
  else if (decode b).isNaN then decode a
  else if decode b<decode a ∨ (a=0 ∧ b=0x8000000000000000) then decode a else decode b

inductive Comparison where
  | gt | le
  deriving DecidableEq, Repr

def Comparison.apply (cmp : Comparison) (a b : Word) : Bool :=
  !(decode a).isNaN && !(decode b).isNaN &&
    (match cmp with | .gt => decide (decode b<decode a) | .le => decide (decode a≤decode b))

/-- Only additional forms needed by the single-thread scalar solver entries.
Base instructions retain their existing semantics, including every load/store. -/
inductive Instr where
  | base (op : Flow.Instr)
  | sqrt (dst : Nat) (a : Operand)
  | abs (dst : Nat) (a : Operand)
  | max (dst : Nat) (a b : Operand)
  | compare (dst : Nat) (cmp : Comparison) (a b : Operand)
  | equal32 (dst : Nat) (a b : Operand)
  | andPred (dst a b : Nat)
  | notPred (dst a : Nat)
  | select32 (dst : Nat) (a b : Operand) (predicate : Nat)
  | move32 (predicate : Nat) (when : Bool) (dst : Nat) (value : Operand)
  | wide4 (dst : Nat) (a : Operand)
  | store32 (address value : Operand)
  | predFP (predicate : Nat) (when : Bool) (op : FP) (dst : Nat) (a b : Operand)
  deriving DecidableEq, Repr

def put32 (s : Flow.State) (address : Nat) (value : BitVec 32) : Flow.State :=
  {s with core:={advance s.core with global:=write32 s.core.global address value}}

def simple (i : Instr) (s : Flow.State) : Flow.State :=
  match i with
  | .wide4 dst a => {s with core:=assign s.core dst (BitVec.ofNat 64 ((Kernel.u32 (a.eval s.core)).toNat*4))}
  | .abs dst a => {s with core:=assign s.core dst (absolute (a.eval s.core))}
  | .compare dst cmp a b => {Flow.next s with predicates:=Function.update s.predicates dst (cmp.apply (a.eval s.core) (b.eval s.core))}
  | .equal32 dst a b => {Flow.next s with predicates:=Function.update s.predicates dst (Kernel.u32 (a.eval s.core)==Kernel.u32 (b.eval s.core))}
  | .andPred dst a b => {Flow.next s with predicates:=Function.update s.predicates dst (s.predicates a && s.predicates b)}
  | .notPred dst a => {Flow.next s with predicates:=Function.update s.predicates dst (!s.predicates a)}
  | .select32 dst a b p => {s with core:=assign s.core dst ((Kernel.u32 ((if s.predicates p then a else b).eval s.core)).setWidth 64)}
  | .move32 p yes dst a => if s.predicates p=yes then {s with core:=assign s.core dst ((Kernel.u32 (a.eval s.core)).setWidth 64)} else Flow.next s
  | _ => s

def ordinary : Instr → Bool
  | .wide4 .. | .abs .. | .compare .. | .equal32 .. | .andPred .. | .notPred .. | .select32 .. | .move32 .. => true
  | _ => false

inductive Eval (ctx : Kernel.Context) : Instr → Flow.State → Flow.State → Prop where
  | base (step : Flow.Eval ctx i s t) : Eval ctx (.base i) s t
  | sqrt (allowed : decode value=Float.sqrt (decode (a.eval s.core))) :
      Eval ctx (.sqrt dst a) s {s with core:=assign s.core dst value}
  | max (allowed : decode value=maximum (a.eval s.core) (b.eval s.core)) :
      Eval ctx (.max dst a b) s {s with core:=assign s.core dst value}
  | simple (plain : ordinary i=true) : Eval ctx i s (simple i s)
  | store32 {addr value : Operand} (valid : Valid32 s.core.globalStart s.core.globalBytes (addr.eval s.core).toNat) :
      Eval ctx (.store32 addr value) s (put32 s (addr.eval s.core).toNat (Kernel.u32 (value.eval s.core)))
  | predFP (enabled : s.predicates p=yes) (allowed : FP.Result op (a.eval s.core) (b.eval s.core) value) :
      Eval ctx (.predFP p yes op dst a b) s {s with core:=assign s.core dst value}
  | skipFP (disabled : s.predicates p≠yes) : Eval ctx (.predFP p yes op dst a b) s (Flow.next s)

def Step (ctx : Kernel.Context) (program : List Instr) (s t : Flow.State) : Prop :=
  s.halted=false ∧ ∃ i, program[s.core.pc]?=some i ∧ Eval ctx i s t

inductive Runs (ctx : Kernel.Context) (program : List Instr) : Flow.State → Flow.State → Prop where
  | nil : Runs ctx program s s
  | cons : Step ctx program s t → Runs ctx program t u → Runs ctx program s u

inductive Sequence (ctx : Kernel.Context) : List Instr → Flow.State → Flow.State → Prop where
  | nil : Sequence ctx [] s s
  | cons {i : Instr} {s middle : Flow.State} {code : List Instr} {t : Flow.State}
      (running : s.halted=false) (step : Eval ctx i s middle) (rest : Sequence ctx code middle t) : Sequence ctx (i::code) s t

def segment : Instr → Bool
  | .base i => Flow.segment i
  | _ => true

end PtxTorchLean.Poisson.PTX.Scalar

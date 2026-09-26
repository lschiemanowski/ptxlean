import PtxBinary32.DenseGlobalReads
import PtxBinary32.DenseArithmetic

/-! Data contracts for the fetched dense program. Arithmetic is relational:
each multiplication and addition retains every result permitted by Results. -/
namespace Ptx.Scalar.Parallel.Dense
open Ptx.Binary32

/-- A scratch value represents the indicated subtree, in its prescribed order. -/
def Node (s : Shape) (global : List Word) (row plane column : Nat) (value : Word) : Prop :=
  Reduction.Eval (Reduction.balanced plane (column*2^plane) (operands s global row)) value

/-- The actual bias addition, followed by the supplied bit-level ReLU. -/
def Output (s : Shape) (global : List Word) (row : Nat) (value : Word) : Prop :=
  ∃ dot affine, Node s global row s.depth 0 dot ∧
    Results .add dot global[s.biasBase+row]! affine ∧ value=Relu.forward affine

theorem node_leaf (s : Shape) (global : List Word) (row column : Nat) (value : Word)
    (allowed : Results .mul (operands s global row column).1 (operands s global row column).2 value) :
    Node s global row 0 column value := by
  simpa [Node,Reduction.balanced] using Reduction.Eval.leaf allowed

theorem node_fork (s : Shape) (global : List Word) (row plane column : Nat) (left right value : Word)
    (hl : Node s global row plane (2*column) left)
    (hr : Node s global row plane (2*column+1) right)
    (allowed : Results .add left right value) : Node s global row (plane+1) column value := by
  have l : (2*column)*2^plane=column*2^(plane+1) := by ring
  have r : (2*column+1)*2^plane=column*2^(plane+1)+2^plane := by ring
  simpa only [Node,Reduction.balanced,l,r] using Reduction.Eval.fork hl hr allowed

/-- Facts required only while a register is live. Registers may otherwise
retain arbitrary caller values or stale values from an earlier stage. -/
structure Data (s : Shape) (global : List Word) (t : Fin s.threads) (a : Scalar.State) : Prop where
  tid : a.regs 0=BitVec.ofNat 32 t.val
  column : 1≤a.pc → a.regs 1=BitVec.ofNat 32 (t.val%s.width)
  productGate : 6≤a.pc → a.pc≤21 → a.preds 0=decide (t.val%s.width<s.columns)
  input : 7≤a.pc → a.pc≤16 → a.regs 4=if a.pc<12 then 0 else (operands s global (t.val/s.width) (t.val%s.width)).2
  weight : 8≤a.pc → a.pc≤16 → a.regs 5=if a.pc<16 then 0 else (operands s global (t.val/s.width) (t.val%s.width)).1
  product : 17≤a.pc → a.pc≤21 → Node s global (t.val/s.width) 0 (t.val%s.width) (a.regs 6)
  roundGate : ∀ k<s.depth, 22+16*k+1≤a.pc → a.pc≤22+16*k+15 →
    a.preds 0=decide (t.val%s.width<2^(s.depth-(k+1)))
  left : ∀ k<s.depth, 22+16*k+8≤a.pc → a.pc≤22+16*k+9 →
    t.val%s.width<2^(s.depth-(k+1)) → Node s global (t.val/s.width) k (2*(t.val%s.width)) (a.regs 4)
  right : ∀ k<s.depth, a.pc=22+16*k+9 →
    t.val%s.width<2^(s.depth-(k+1)) → Node s global (t.val/s.width) k (2*(t.val%s.width)+1) (a.regs 5)
  reduced : ∀ k<s.depth, 22+16*k+10≤a.pc → a.pc≤22+16*k+15 →
    t.val%s.width<2^(s.depth-(k+1)) → Node s global (t.val/s.width) (k+1) (t.val%s.width) (a.regs 6)
  outputGate : 22+16*s.depth+1≤a.pc → a.pc≤22+16*s.depth+19 → a.preds 0=decide (t.val%s.width=0)
  root : 22+16*s.depth+6≤a.pc → a.pc≤22+16*s.depth+11 → t.val%s.width=0 →
    Node s global (t.val/s.width) s.depth 0 (a.regs 6)
  bias : a.pc=22+16*s.depth+11 → t.val%s.width=0 → a.regs 8=global[s.biasBase+t.val/s.width]!
  affine : 22+16*s.depth+12≤a.pc → a.pc≤22+16*s.depth+13 → t.val%s.width=0 →
    ∃ dot, Node s global (t.val/s.width) s.depth 0 dot ∧ Results .add dot global[s.biasBase+t.val/s.width]! (a.regs 6)
  sign : a.pc=22+16*s.depth+13 → a.preds 1=decide ((a.regs 6).toNat≥2147483648)
  output : 22+16*s.depth+14≤a.pc → a.pc≤22+16*s.depth+19 → t.val%s.width=0 → Output s global (t.val/s.width) (a.regs 6)

/-- The value of an actual load, classified by its fetched site. -/
def ReadData (s : Shape) (global : List Word) (t : Fin s.threads) (pc : Nat) (value : Word) : Prop :=
  (pc=11 → value=global[t.val%s.width]!) ∧
  (pc=15 → value=global[s.weight (t.val/s.width) (t.val%s.width)]!) ∧
  (∀ k<s.depth, pc=22+16*k+7 → Node s global (t.val/s.width) k (2*(t.val%s.width)) value) ∧
  (∀ k<s.depth, pc=22+16*k+8 → Node s global (t.val/s.width) k (2*(t.val%s.width)+1) value) ∧
  (pc=22+16*s.depth+5 → Node s global (t.val/s.width) s.depth 0 value) ∧
  (pc=22+16*s.depth+10 → value=global[s.biasBase+t.val/s.width]!)

/-- The value of an actual store, classified by its fetched site. -/
def StoreData (s : Shape) (global : List Word) (t : Fin s.threads) (pc : Nat) (value : Word) : Prop :=
  (pc=20 → Node s global (t.val/s.width) 0 (t.val%s.width) value) ∧
  (∀ k<s.depth, pc=22+16*k+14 → Node s global (t.val/s.width) (k+1) (t.val%s.width) value) ∧
  (pc=22+16*s.depth+18 → Output s global (t.val/s.width) value)

theorem initial_data (s : Shape) (global shared : List Word) (seeds : Fin s.threads → Scalar.State) (t : Fin s.threads) :
    Data s global t ((initial s global shared seeds).lanes t).scalar := by
  constructor <;> simp [initial,Scalar.update]

end Ptx.Scalar.Parallel.Dense

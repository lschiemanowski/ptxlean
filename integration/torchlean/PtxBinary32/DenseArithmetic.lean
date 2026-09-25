import PtxBinary32.DenseLayout
import PtxBinary32.ReductionRelu

/-! Arithmetic indexed exactly as the fresh shared planes. These are reduction
facts; a fetched execution must still establish that each stored node has the
corresponding value. No memory observation is assumed by this module. -/
namespace Ptx.Scalar.Parallel.Dense
open Ptx.Binary32

def operands (s : Shape) (global : List Word) (row column : Nat) : Word × Word :=
  if column < s.columns then (global[s.weight row column]!,global[column]!) else (0,0)

def nodeValue (s : Shape) (global : List Word) (row : Nat) : Nat → Nat → Word
  | 0,column => reference .mul (operands s global row column).1 (operands s global row column).2
  | round+1,column => reference .add (nodeValue s global row round (2*column))
      (nodeValue s global row round (2*column+1))

def affineWord (s : Shape) (global : List Word) (row : Nat) : Word :=
  reference .add (nodeValue s global row s.depth 0) global[s.biasBase+row]!

def forwardWord (s : Shape) (global : List Word) (row : Nat) : Word :=
  Relu.forward (affineWord s global row)

theorem node_tree (s : Shape) (global : List Word) (row round column : Nat) :
    Reduction.Eval (Reduction.balanced round (column*2^round) (operands s global row))
      (nodeValue s global row round column) := by
  induction round generalizing column with
  | zero => simpa [Reduction.balanced,nodeValue] using
      Reduction.Eval.leaf (envelope_self (reference .mul (operands s global row column).1 (operands s global row column).2))
  | succ k ih =>
    have left := ih (2*column)
    have right := ih (2*column+1)
    have hl : (2*column)*2^k = column*2^(k+1) := by ring
    have hr : (2*column+1)*2^k = column*2^(k+1)+2^k := by ring
    rw [hl] at left
    rw [hr] at right
    exact .fork left right (envelope_self _)

theorem forward_accuracy (s : Shape) (global : List Word) (row : Nat)
    (i : Reduction.RowInput)
    (tree : Reduction.words i.tree = Reduction.balanced s.depth 0 (operands s global row))
    (bias : i.bias = global[s.biasBase+row]!) :
    finiteReal (forwardWord s global row) = some (max i.affine 0) ∧
      |max i.affine 0-max i.idealAffine 0| ≤ i.error := by
  apply Reduction.row_forward_accuracy i
  refine ⟨nodeValue s global row s.depth 0,?_,?_⟩
  · rw [tree]; simpa using node_tree s global row s.depth 0
  · rw [bias]; exact envelope_self _

end Ptx.Scalar.Parallel.Dense

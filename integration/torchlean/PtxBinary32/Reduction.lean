import PtxBinary32.DotError

/-! Balanced binary32 arithmetic trees. These relations specify arithmetic
choices, not thread execution; the parallel machine supplies instruction origin. -/
namespace Ptx.Binary32.Reduction
open TorchLean.Floats (eps32)
open TorchLean.Floats.IEEE754.IEEE32Exec (fp32Round)

inductive Tree (α : Type) where
  | leaf (value : α)
  | fork (left right : Tree α)
  deriving Repr

def Tree.map (f : α → β) : Tree α → Tree β
  | .leaf x => .leaf (f x)
  | .fork a b => .fork (a.map f) (b.map f)

def Tree.leaves : Tree α → List α
  | .leaf x => [x]
  | .fork a b => a.leaves ++ b.leaves

def Tree.depth : Tree α → Nat
  | .leaf _ => 0
  | .fork a b => 1 + max a.depth b.depth

/-- Equal-sized subtrees, with consecutive indices and a fixed left/right order. -/
def balanced (depth offset : Nat) (f : Nat → α) : Tree α :=
  match depth with
  | 0 => .leaf (f offset)
  | depth+1 => .fork (balanced depth offset f) (balanced depth (offset+2^depth) f)

theorem balanced_depth (d offset : Nat) (f : Nat → α) : (balanced d offset f).depth = d := by
  induction d generalizing offset with
  | zero => rfl
  | succ d ih => simp [balanced,Tree.depth,ih,Nat.add_comm]

theorem balanced_leaves (d offset : Nat) (f : Nat → α) :
    (balanced d offset f).leaves = (List.range (2^d)).map (fun i => f (offset+i)) := by
  induction d generalizing offset with
  | zero => simp [balanced,Tree.leaves]
  | succ d ih =>
    rw [balanced,Tree.leaves,ih,ih]
    rw [pow_succ,Nat.mul_two,List.range_add,List.map_append,List.map_map]
    congr 1
    simp [Function.comp_def,Nat.add_assoc]

/-- One rounded multiplication at each leaf, one rounded addition at each fork. -/
inductive Eval : Tree (Word × Word) → Word → Prop
  | leaf : Results .mul a b out → Eval (.leaf (a,b)) out
  | fork : Eval a left → Eval b right → Results .add left right out → Eval (.fork a b) out

theorem eval_exists (tree : Tree (Word × Word)) : ∃ out, Eval tree out := by
  induction tree with
  | leaf p => obtain ⟨out,h⟩ := results_exists .mul p.1 p.2; exact ⟨out,.leaf h⟩
  | fork a b ihA ihB =>
    obtain ⟨left,hl⟩ := ihA
    obtain ⟨right,hr⟩ := ihB
    obtain ⟨out,ho⟩ := results_exists .add left right
    exact ⟨out,.fork hl hr ho⟩

noncomputable def ideal : Tree DotError.Input → ℝ
  | .leaf x => x.l*x.r
  | .fork a b => ideal a + ideal b

noncomputable def rounded : Tree DotError.Input → ℝ
  | .leaf x => fp32Round (x.lh*x.rh)
  | .fork a b => fp32Round (rounded a+rounded b)

/-- Finiteness checks use only the initial operands and the fixed rounded tree. -/
def Safe : Tree DotError.Input → Prop
  | .leaf _ => True
  | .fork a b => Safe a ∧ Safe b ∧ |rounded a+rounded b| ≤ Bounds.maxFinite

noncomputable def budget : Tree DotError.Input → ℝ
  | .leaf x => eps32 (x.lh*x.rh)+|x.l| *x.er+|x.r| *x.el+x.el*x.er
  | .fork a b => eps32 (rounded a+rounded b)+budget a+budget b

def words (tree : Tree DotError.Input) := tree.map fun x => (x.left,x.right)

/-- All admitted arithmetic choices obey the same finite-value and error contract. -/
theorem accuracy (tree : Tree DotError.Input) (safe : Safe tree) (allowed : Eval (words tree) out) :
    finiteReal out = some (rounded tree) ∧ |rounded tree-ideal tree| ≤ budget tree := by
  induction tree generalizing out with
  | leaf x =>
    cases allowed with
    | leaf allowed =>
      have value := Bounds.round_of_range .mul x.left x.right out x.lh x.rh
        x.leftReal x.rightReal x.productRange allowed
      obtain ⟨_,z,hz,error⟩ := Error.mul_results x.left x.right out x.lh x.rh x.l x.r x.el x.er
        x.leftReal x.rightReal x.productRange x.leftError x.rightError allowed
      have eq : z = rounded (.leaf x) := Option.some.inj (hz.symm.trans value)
      exact ⟨value,by simpa [eq,ideal,budget] using error⟩
  | fork a b ihA ihB =>
    cases allowed with
    | @fork _ left _ right _ leftEval rightEval allowed =>
      obtain ⟨hl,el⟩ := ihA safe.1 leftEval
      obtain ⟨hr,er⟩ := ihB safe.2.1 rightEval
      have value := Bounds.round_of_range .add left right out (rounded a) (rounded b) hl hr safe.2.2 allowed
      obtain ⟨_,z,hz,error⟩ := Error.add_results left right out (rounded a) (rounded b)
        (ideal a) (ideal b) (budget a) (budget b) hl hr safe.2.2 el er allowed
      have eq : z = rounded (.fork a b) := Option.some.inj (hz.symm.trans value)
      exact ⟨value,by simpa [eq,ideal,budget] using error⟩

theorem ideal_leaves (tree : Tree DotError.Input) :
    ideal tree = (tree.leaves.map fun x => x.l*x.r).sum := by
  induction tree <;> simp_all [ideal,Tree.leaves,List.sum_append]

end Ptx.Binary32.Reduction

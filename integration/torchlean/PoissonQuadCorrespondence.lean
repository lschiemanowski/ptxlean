import PoissonQuad
import PoissonBinary64
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum

/-! Ordered algorithm lemmas for the Poisson backend. These are NOT an
instruction-execution theorem. In particular, byte addresses and barriers are
not erased into hypotheses claiming that a kernel already computes its result. -/
namespace PtxTorchLean.Poisson.Correspondence
open TorchLean

/-- Four scalar registers used by one unrolled contraction. -/
structure Registers (α : Type) where
  left : α
  right : α
  product : α
  accumulator : α

/-- Instruction-level arithmetic within an already supplied scalar stream.
Loads here select a scalar input, not a byte address. -/
inductive Op (α : Type) where
  | loadLeft (value : α)
  | loadRight (value : α)
  | multiply
  | accumulate

def step [Mul α] [Add α] (s : Registers α) : Op α → Registers α
  | .loadLeft x => { s with left := x }
  | .loadRight x => { s with right := x }
  | .multiply => { s with product := s.left * s.right }
  | .accumulate => { s with accumulator := s.accumulator + s.product }

def run [Mul α] [Add α] (code : List (Op α)) (s : Registers α) : Registers α :=
  code.foldl step s

def contractionCode (pairs : List (α × α)) : List (Op α) :=
  pairs.flatMap fun (a,b) => [.loadLeft a, .loadRight b, .multiply, .accumulate]

/-- Separate multiply/add instructions recover exactly the specified left fold;
no algebraic law about either operation is assumed. -/
theorem contraction_correct [Mul α] [Add α] (pairs : List (α × α)) (s : Registers α) :
    (run (contractionCode pairs) s).accumulator =
      pairs.foldl (fun acc p => acc + p.1 * p.2) s.accumulator := by
  induction pairs generalizing s with
  | nil => rfl
  | cons p ps ih =>
    simpa [contractionCode, run, List.foldl_append, step] using
      ih { s with left := p.1, right := p.2, product := p.1*p.2,
                   accumulator := s.accumulator+p.1*p.2 }

abbrev Grid (α : Type) (n : Nat) := Fin n → Fin n → α

def contraction [Mul α] [Add α] [Zero α] (a b : Fin n → α) : α :=
  (run (contractionCode ((List.finRange n).map fun k => (a k,b k)))
    ⟨0,0,0,0⟩).accumulator

theorem contraction_eq_fold [Mul α] [Add α] [Zero α] (a b : Fin n → α) :
    contraction a b = (List.finRange n).foldl (fun acc k => acc + a k*b k) 0 := by
  simp [contraction, contraction_correct, List.foldl_map]

def product [Mul α] [Add α] [Zero α] (a b : Grid α n) : Grid α n :=
  fun i j => contraction (a i) (fun k => b k j)

def transposed (a : Grid α n) : Grid α n := fun i j => a j i
def weighted [Mul α] (w a : Grid α n) : Grid α n := fun i j => w i j * a i j
def summed [Add α] (a b : Grid α n) : Grid α n := fun i j => a i j + b i j

def entries [Storage α] (a : Mat α n n) : Grid α n := fun i j => Spec.get2 a i j

@[simp] theorem entries_matrix [Storage α] (a : Grid α n) : entries (matrix a) = a := by
  funext i j
  simp [entries, matrix, Spec.get2, Spec.get, Tensor.getScalar, Tensor.unstack, Tensor.item]

theorem entries_product [Storage α] [Mul α] [Add α] [Zero α] (a b : Mat α n n) :
    entries (Spec.matMulSpec a b) = product (entries a) (entries b) := by
  funext i j
  simp [entries, product, contraction_eq_fold, Spec.matMulSpec,
    Spec.get2, Spec.get, Tensor.getScalar, Tensor.unstack, Tensor.item]

@[simp] theorem entries_transpose [Storage α] (a : Mat α n n) :
    entries (transpose a) = transposed (entries a) := by
  change entries (matrix _) = _
  rw [entries_matrix]
  rfl

@[simp] theorem entries_weighted [Storage α] [Mul α] (w a : Mat α n n) :
    entries (hadamard w a) = weighted (entries w) (entries a) := by
  change entries (matrix _) = _
  rw [entries_matrix]
  rfl

@[simp] theorem entries_summed [Storage α] [Add α] (a b : Mat α n n) :
    entries (plus a b) = summed (entries a) (entries b) := by
  change entries (matrix _) = _
  rw [entries_matrix]
  rfl

/-- Seven shared planes at phase boundaries; plane zero is the gathered input. -/
structure Planes (α : Type) (n : Nat) where
  u : Grid α n
  bu : Grid α n
  du : Grid α n
  dx : Grid α n
  dy : Grid α n
  bl : Grid α n
  dl : Grid α n

def phase1 (u : Grid α n) [Zero α] : Planes α n :=
  ⟨u,fun _ _ => 0,fun _ _ => 0,fun _ _ => 0,fun _ _ => 0,fun _ _ => 0,fun _ _ => 0⟩
def phase2 [Mul α] [Add α] [Zero α] (b d : Grid α n) (s : Planes α n) : Planes α n :=
  { s with bu := product b s.u, du := product d s.u }
def phase3 [Mul α] [Add α] [Zero α] (b d w : Grid α n) (s : Planes α n) : Planes α n :=
  { s with dx := fun i j => product s.bu (transposed d) i j * w i j,
           dy := fun i j => product s.du (transposed b) i j * w i j }
def phase4 [Mul α] [Add α] [Zero α] (b d : Grid α n) (s : Planes α n) : Planes α n :=
  { s with bl := product (transposed b) s.dx, dl := product (transposed d) s.dy }
def phase5 [Mul α] [Add α] [Zero α] (b d : Grid α n) (s : Planes α n) : Grid α n :=
  summed (product s.bl d) (product s.dl b)

def cell [Mul α] [Add α] [Zero α] (b d w u : Grid α n) : Grid α n :=
  phase5 b d (phase4 b d (phase3 b d w (phase2 b d (phase1 u))))

/-- Arbitrary tensors, including non-associative arithmetic: the ordered phase
calculation agrees with the existing TorchLean definition. Only operand
commutation for the weight product is needed; native Float discharges it below. -/
theorem cell_correspondence [Storage α] [Mul α] [Add α] [Zero α]
    (commute : ∀ a b : α, a*b=b*a) (b d w u : Mat α n n) :
    cell (entries b) (entries d) (entries w) (entries u) =
      entries (localAction b d w u) := by
  simp only [localAction, entries_summed, entries_product, entries_transpose, entries_weighted]
  simp only [cell, phase1, phase2, phase3, phase4, phase5]
  simp_rw [commute (product (product (entries b) (entries u)) (transposed (entries d)) _ _) (entries w _ _),
    commute (product (product (entries d) (entries u)) (transposed (entries b)) _ _) (entries w _ _)]
  rfl

/-- The actual logical native-Float tensor definition, not a replacement real
matrix specification. No associativity of rounded addition is used. -/
theorem cell_float_correspondence (b d w u : Mat Float n n) :
    cell (entries b) (entries d) (entries w) (entries u) =
      entries (localAction b d w u) :=
  cell_correspondence Binary64.mul_comm b d w u

/-- Assembly is a fold of updates to independently indexed nodes. -/
def scatterStep [DecidableEq ι] [Add α] (s : ι → α) (entry : ι × α) : ι → α :=
  Function.update s entry.1 (s entry.1 + entry.2)

/-- Removing other nodes' contributions preserves a node's exact accumulation
order, without assuming associativity or commutativity of addition. -/
theorem scatter_gather [DecidableEq ι] [Add α]
    (contributions : List (ι × α)) (s : ι → α) (node : ι) :
    (contributions.foldl scatterStep s) node =
      (contributions.filter fun entry => entry.1 == node).foldl
        (fun acc entry => acc + entry.2) (s node) := by
  induction contributions generalizing s with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.foldl_cons, ih]
    by_cases h : x.1 = node
    · simp [h, scatterStep]
    · simp [h, scatterStep, Function.update_of_ne (Ne.symm h)]

/-- The final one-writer-per-node assembly map, independent of node scheduling. -/
def assemble [DecidableEq ι] [Add α] [Zero α]
    (contributions : List (ι × α)) (node : ι) : α :=
  (contributions.filter fun entry => entry.1 == node).foldl (fun acc entry => acc + entry.2) 0

theorem assembly_correspondence [DecidableEq ι] [Add α] [Zero α]
    (contributions : List (ι × α)) :
    assemble contributions = contributions.foldl scatterStep (fun _ => 0) := by
  funext node
  exact (scatter_gather contributions (fun _ => 0) node).symm

/-- Writes to distinct output nodes commute even for non-associative scalars. -/
theorem distinct_writers_commute [DecidableEq ι] (s : ι → α) (i j : ι)
    (hi : i ≠ j) (x y : α) :
    Function.update (Function.update s i x) j y =
      Function.update (Function.update s j y) i x := by
  exact Function.update_comm hi x y s

/-- A shape-safe mesh adapter. The connectivity is shared by both calculations;
its relationship to serialized Python/Lean array indices is a separate layer. -/
structure Connectivity (elements width nodes : Nat) where
  node : Fin elements → Fin width → Fin width → Fin nodes

def gathered (mesh : Connectivity e n v) (values : Fin v → α) (element : Fin e) : Grid α n :=
  fun i j => values (mesh.node element i j)

/-- Contributions retain element-major, then row-major order. -/
def contributions (mesh : Connectivity e n v) (localValues : Fin e → Grid α n) :
    List (Fin v × α) :=
  (List.finRange e).flatMap fun element =>
    (List.finRange n).flatMap fun i =>
      (List.finRange n).map fun j => (mesh.node element i j,localValues element i j)

def operator [Storage α] [Add α] [Mul α] [Zero α]
    (mesh : Connectivity e n v) (b d w : Mat α n n) (values : Fin v → α) : Fin v → α :=
  assemble (contributions mesh fun element =>
    cell (entries b) (entries d) (entries w) (gathered mesh values element))

def tensorContributions [Storage α] [Add α] [Mul α] [Zero α]
    (mesh : Connectivity e n v) (b d w : Mat α n n) (values : Fin v → α) : List (Fin v × α) :=
  let locals := Array.ofFn fun element : Fin e =>
    localAction b d w (matrix (gathered mesh values element))
  contributions mesh fun element => entries (locals[element.val]'(by simpa [locals] using element.isLt))

def tensorOperator [Storage α] [Add α] [Mul α] [Zero α]
    (mesh : Connectivity e n v) (b d w : Mat α n n) (values : Fin v → α) : Fin v → α :=
  (tensorContributions mesh b d w values).foldl scatterStep (fun _ => 0)

/-- All cells and all nodes, with rounded accumulation order retained. This is
an algorithmic correspondence, not a theorem about fetched PTX instructions. -/
theorem operator_correspondence [Storage α] [Add α] [Mul α] [Zero α]
    (commute : ∀ a b : α, a*b=b*a) (mesh : Connectivity e n v)
    (b d w : Mat α n n) (values : Fin v → α) :
    operator mesh b d w values = tensorOperator mesh b d w values := by
  have h (element : Fin e) :
      cell (entries b) (entries d) (entries w) (gathered mesh values element) =
        entries (localAction b d w (matrix (gathered mesh values element))) := by
    simpa only [entries_matrix] using
      cell_correspondence commute b d w (matrix (gathered mesh values element))
  simp only [operator, h, assembly_correspondence, tensorOperator, tensorContributions, Array.getElem_ofFn]

theorem operator_float_correspondence (mesh : Connectivity e n v)
    (b d w : Mat Float n n) (values : Fin v → Float) :
    operator mesh b d w values = tensorOperator mesh b d w values :=
  operator_correspondence Binary64.mul_comm mesh b d w values

/-- Boundary masking is preserved by the operator correspondence. -/
theorem interior_float_correspondence (mesh : Connectivity e n v)
    (b d w : Mat Float n n) (values : Fin v → Float) (boundary : Fin v → Bool) :
    zeroBoundary boundary (operator mesh b d w (zeroBoundary boundary values)) =
      zeroBoundary boundary (tensorOperator mesh b d w (zeroBoundary boundary values)) := by
  rw [operator_float_correspondence]

/-- Every row-major coordinate used by a live matrix lane lies in its plane. -/
theorem row_major_bound (i j : Fin n) : i.val*n+j.val < n*n := by
  have h := Nat.mul_le_mul_right n (Nat.succ_le_of_lt i.isLt)
  simp only [Nat.succ_mul] at h
  have hj := j.isLt
  omega

/-- Distinct live lanes cannot write the same scalar within a plane. -/
theorem row_major_injective (i j k l : Fin n)
    (h : i.val*n+j.val = k.val*n+l.val) : i=k ∧ j=l := by
  have hi : (i.val*n+j.val)/n=i.val := by
    rw [Nat.mul_comm i.val n, Nat.mul_add_div (Nat.zero_lt_of_lt j.isLt), Nat.div_eq_of_lt j.isLt, Nat.add_zero]
  have hk : (k.val*n+l.val)/n=k.val := by
    rw [Nat.mul_comm k.val n, Nat.mul_add_div (Nat.zero_lt_of_lt l.isLt), Nat.div_eq_of_lt l.isLt, Nat.add_zero]
  have hh : i.val=k.val := by rw [← hi, ← hk, h]
  constructor
  · exact Fin.ext hh
  · apply Fin.ext
    rw [hh] at h
    omega

/-- The seven planes used for Q1–Q4 fit in the declared shared-memory allocation. -/
theorem shared_offset_bound (width : Nat) (hw : 2 ≤ width ∧ width ≤ 5)
    (plane : Fin 7) (i j : Fin width) :
    8*(plane.val*(width*width)+(i.val*width+j.val))+8 ≤ 1400 := by
  have hcoord := row_major_bound i j
  have hp := plane.isLt
  rcases hw with ⟨hwlo,hwhi⟩
  interval_cases width <;> norm_num at * <;> omega

end PtxTorchLean.Poisson.Correspondence

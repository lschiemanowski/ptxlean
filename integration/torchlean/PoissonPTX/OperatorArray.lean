import PoissonPTX.OperatorMesh

namespace PtxTorchLean.Poisson.PTX.ArrayOperator
open Correspondence

/-- Proof view of the reference's private array scatter, retaining its exact
loop order and rounded update. Its connection to the public entry is proved below. -/
def scatter (cells : Array (Array Nat)) (locals : Array (Array Float)) (size : Nat) : Array Float := Id.run do
  let mut out := Array.replicate size 0.0
  for e in [0:cells.size] do
    for i in [0:cells[e]!.size] do
      let j := (cells[e]!)[i]!
      out := out.set! j (out[j]!+(locals[e]!)[i]!)
  return out

def flat (a : Mat Float m n) : Array Float :=
  (Array.range (m*n)).map fun k =>
    if hi : k/n<m then if hj : k%n<n then Spec.get2 a ⟨k/n,hi⟩ ⟨k%n,hj⟩ else 0 else 0

def localValues (o : Operator) (values : Array Float) : Array (Array Float) :=
  (Array.range o.mesh.cells.size).map fun e => flat (localAction o.b o.d o.w (gather o values e))

def result (o : Operator) (values : Array Float) : Array Float :=
  scatter o.mesh.cells (localValues o values) o.mesh.points.size

/-- This is the actual public reference function, including its existing
length and finiteness validation, not a separately assumed operator result. -/
theorem apply_valid (o : Operator) (values : Array Float)
    (size : values.size=o.mesh.points.size) (finite : values.all Float.isFinite=true) :
    Poisson.apply o values=.ok (result o values) := by
  change ((do
    if values.size != o.mesh.points.size then
      throw s!"expected vector of length {o.mesh.points.size}, got {values.size}"
    if !(values.all Float.isFinite) then throw "vector must be finite"
    pure () : Except String Unit) >>= fun _ => pure (result o values)) = _
  simp only [finite]
  simp [size]
  rfl

def addAt (out : Array Float) (item : Nat × Float) : Array Float :=
  out.set! item.1 (out[item.1]!+item.2)

def contributions (cells : Array (Array Nat)) (locals : Array (Array Float)) : List (Nat × Float) :=
  (List.range cells.size).flatMap fun e => (List.range cells[e]!.size).map fun i => ((cells[e]!)[i]!, (locals[e]!)[i]!)

theorem scatter_fold (cells : Array (Array Nat)) (locals : Array (Array Float)) (size : Nat) :
    scatter cells locals size=(contributions cells locals).foldl addAt (Array.replicate size 0) := by
  change scatter cells locals size=(contributions cells locals).foldl addAt (Array.replicate size 0.0)
  simp [scatter,contributions,addAt,List.forIn_pure_yield_eq_foldl,List.foldl_flatMap,List.foldl_map,List.range_eq_range']

@[simp] theorem addAt_size (out : Array Float) (item : Nat × Float) :
    (addAt out item).size=out.size := by simp [addAt]

theorem addAt_get (out : Array Float) (item : Nat × Float) (i : Nat) (inside : i<out.size) :
    (addAt out item)[i]! = if item.1=i then out[i]!+item.2 else out[i]! := by
  simp only [addAt,Array.set!_eq_setIfInBounds]
  rw [getElem!_pos _ _ (by simpa using inside),Array.getElem_setIfInBounds inside]
  by_cases eq : item.1=i
  · simp [eq,inside]
  · simp [eq,inside]

theorem fold_size (items : List (Nat × Float)) (out : Array Float) :
    (items.foldl addAt out).size=out.size := by
  induction items generalizing out with
  | nil => rfl
  | cons item rest ih => simp [List.foldl_cons,ih]

/-- Array mutation and function update agree at every allocated coordinate.
No associativity of addition is required. -/
theorem fold_get (items : List (Nat × Float)) (out : Array Float) (state : Nat → Float)
    (same : ∀ i<out.size, out[i]! = state i) (i : Nat) (inside : i<out.size) :
    (items.foldl addAt out)[i]! = items.foldl scatterStep state i := by
  induction items generalizing out state with
  | nil => exact same i inside
  | cons item rest ih =>
    simp only [List.foldl_cons]
    apply ih (addAt out item) (scatterStep state item) _ (by simpa using inside)
    intro j hj
    have hj' : j<out.size := by simpa using hj
    rw [addAt_get out item j hj']
    by_cases eq : item.1=j
    · subst j; simp [scatterStep,same _ hj']
    · simp [eq,scatterStep,Function.update_of_ne (Ne.symm eq),same _ hj']

end PtxTorchLean.Poisson.PTX.ArrayOperator

import PoissonQuadCorrespondence

namespace PtxTorchLean.Poisson.PTX.Assembly.Rows

/-- Each pair names a mesh node and its position in the flat cell-value array.
Filtering preserves the element-major and row-major order of this input list. -/
def selected (locations : List (Nat × Nat)) (node : Nat) : List Nat :=
  (locations.filter fun item => item.1==node).map Prod.snd

def contributions (locations : List (Nat × Nat)) (values : Nat → Float) : List (Nat × Float) :=
  locations.map fun item => (item.1,values item.2)

/-- Filtering cells into one node's index list preserves precisely the ordered
scatter sum. No associativity, commutativity or reassociation is used. -/
theorem ordered (locations : List (Nat × Nat)) (values : Nat → Float) (node : Nat) :
    (selected locations node).foldl (fun acc k => acc+values k) 0=
      (contributions locations values).foldl Correspondence.scatterStep (fun _ => 0) node := by
  rw [Correspondence.scatter_gather]
  have general : ∀ (xs : List (Nat × Nat)) (acc : Float),
      (selected xs node).foldl (fun acc k => acc+values k) acc=
        ((contributions xs values).filter fun item => item.1==node).foldl (fun acc item => acc+item.2) acc := by
    intro xs
    induction xs with
    | nil => intro acc; rfl
    | cons item rest ih =>
      intro acc
      by_cases same : item.1=node
      · simpa [selected,contributions,same] using ih (acc+values item.2)
      · simpa [selected,contributions,same] using ih acc
  exact general locations 0

/-- Concrete regression with two interleaved nodes and an order-sensitive sum. -/
theorem interleaved :
    selected [(0,0),(1,1),(0,2),(1,3),(0,4)] 0=[0,2,4] ∧
    selected [(0,0),(1,1),(0,2),(1,3),(0,4)] 1=[1,3] := by decide +kernel

end PtxTorchLean.Poisson.PTX.Assembly.Rows

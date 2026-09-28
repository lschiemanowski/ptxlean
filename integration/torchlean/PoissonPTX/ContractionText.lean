import PoissonPTX.SharedStore
import PoissonPTX.Text
import PoissonPTX.Contraction

namespace PtxTorchLean.Poisson.PTX.Contraction

structure Plan where
  name : String
  acc : Nat
  left : Matrix
  right : Matrix
  deriving DecidableEq, Repr

/-- The eight actual contractions in the four arithmetic phases. Plane zero
contains gathered input; establishing its contents and barriers remains separate. -/
def plans (width : Nat) (b d : Word) : List Plan :=
  let plane (p : Nat) := BitVec.ofNat 64 (p*width*width*8)
  [⟨"bu",8,⟨.global,b,.row,.inner⟩,⟨.shared,plane 0,.inner,.column⟩⟩,
   ⟨"du",8,⟨.global,d,.row,.inner⟩,⟨.shared,plane 0,.inner,.column⟩⟩,
   ⟨"dx",8,⟨.shared,plane 1,.row,.inner⟩,⟨.global,d,.column,.inner⟩⟩,
   ⟨"dy",8,⟨.shared,plane 2,.row,.inner⟩,⟨.global,b,.column,.inner⟩⟩,
   ⟨"bl",8,⟨.global,b,.inner,.row⟩,⟨.shared,plane 3,.inner,.column⟩⟩,
   ⟨"dl",8,⟨.global,d,.inner,.row⟩,⟨.shared,plane 4,.inner,.column⟩⟩,
   ⟨"x",8,⟨.shared,plane 5,.row,.inner⟩,⟨.global,d,.inner,.column⟩⟩,
   ⟨"y",9,⟨.shared,plane 6,.row,.inner⟩,⟨.global,b,.inner,.column⟩⟩]

theorem plans_accumulator (p : Plan) (h : p∈plans width b d) : Accumulator p.acc := by
  simp only [plans,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> simp [Accumulator]

/-- mov.f64 with a zero bit literal has the bit-copy semantics of Op.mov. -/
def render (op : Op) : String :=
  match op with
  | .mov dst (.imm w) =>
    if w=0 then s!"mov.f64 {Text.register dst}, 0d0000000000000000;" else Text.data op
  | _ => Text.data op

/-- Render the same program consumed by fetched_correct, not a second algorithm. -/
def rendered (width : Nat) (b d : Word) : List (String × List String) :=
  (plans width b d).map fun p => (p.name,(program width p.acc p.left p.right).map render)

/-- Seven emitted shared-store blocks: gathered input, then six intermediate planes. -/
def renderedStores (width : Nat) : List (Nat × List String) :=
  (List.range 7).map fun plane => (plane,
    (SharedStore.code (BitVec.ofNat 64 (plane*width*width*8))
      (if plane=0 then 11 else 8)).map Text.data)

end PtxTorchLean.Poisson.PTX.Contraction

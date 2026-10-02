import PoissonPTX.CellTailProgram
import PoissonPTX.CellEntryText

namespace PtxTorchLean.Poisson.PTX.CellWhole

/-- Native-counter control facts computed from the fetched Lean instruction
lists. PTX labels are zero-length markers and are not instructions. -/
def shape (width : Nat) (cells source output : Word) : Nat × List Nat × List (Nat × Nat) :=
  let entry := CellEntry.program width cells source
  let front := Concurrent.CellConsumer.WithOutput.front width
  let barriers := (entry.zipIdx.filterMap fun (op,pc) => match op with
    | .sync => some pc | _ => none) ++
    (front.zipIdx.filterMap fun (op,pc) => match op with
      | .sync _ => some (entry.length+pc) | _ => none)
  let branches := (entry.zipIdx.filterMap fun (op,pc) => match op with
    | .skip target => some (pc,target) | _ => none) ++
    (front.zipIdx.filterMap fun (op,pc) => match op with
      | .skip _ target => some (entry.length+pc,entry.length+target) | _ => none)
  (entry.length+front.length+(CellFinal.tail width output).length,barriers,branches)

end PtxTorchLean.Poisson.PTX.CellWhole

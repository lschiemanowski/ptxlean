import PoissonPTX.AssemblyMeshRows
import PoissonPTX.AssemblyTableConstruction

namespace PtxTorchLean.Poisson.PTX.Assembly
open Correspondence

/-- Given published cell values as the input bytes of this launch, the actual
parallel assembly computes the TorchLean tensor operator. Integer table
representation establishes traversal and safety; no assembled result is a
premise. Cell publication and inter-launch transport are distinct preceding
obligations, represented here by the cell-value input contract. -/
theorem Arena.parallel_operator {a : Arena v} {memory : Memory} {regs : Fin v → Registers}
    {words : List (Concurrent.Event v)} {indices : List (Fin v × IndexSources.Access)} {final : Fin v → Flow.State}
    (mesh : Connectivity e w v) (b d weight : Mat Float w w) (input : Fin v → Float)
    (run : Flow.Parallel.Runs a.context
      (entryCode (BitVec.ofNat 32 v) a.offsets a.entries a.element mask a.boundary a.output)
      (fun i => a.start memory (regs i)) words indices final)
    (compatible : Concurrent.Visibility.Compatible (fun space => match space with | .global => memory | .shared => fun _ => 0) words wordSource)
    (indexCompatible : IndexSources.Compatible memory words indices indexSource)
    (tables : a.RowsEncoded memory (nodeRows v (MeshRows.locations mesh)))
    (separated : a.InputSeparation) (done : ∀ i, (final i).halted=true)
    (cells : ∀ element i j, a.elementValue memory (element.val*(w*w)+i.val*w+j.val)=
      Correspondence.entries (localAction b d weight (matrix (gathered mesh input element))) i j)
    (node : Fin v) :
    decode (read64 (Concurrent.GlobalPublication.publish memory words) (Snapshot.address a node))=
      if mask=true ∧ read32 memory (a.base.toNat+a.boundary.toNat+node.val*4)≠0 then 0 else
        tensorOperator mesh b d weight input node := by
  rw [a.parallel_scatter run compatible indexCompatible tables.contents separated done
    (MeshRows.locations mesh) tables.selected node]
  rw [MeshRows.operator_sum mesh _ b d weight input cells node]

/-- The unmasked probe and boundary-masked operator use the same ordered
calculation. This theorem expresses masking through the represented mesh's
Boolean boundary function instead of raw flag words. -/
theorem Arena.parallel_masked_operator {a : Arena v} {memory : Memory} {regs : Fin v → Registers}
    {words : List (Concurrent.Event v)} {indices : List (Fin v × IndexSources.Access)} {final : Fin v → Flow.State}
    (mesh : Connectivity e w v) (b d weight : Mat Float w w) (input : Fin v → Float)
    (run : Flow.Parallel.Runs a.context
      (entryCode (BitVec.ofNat 32 v) a.offsets a.entries a.element true a.boundary a.output)
      (fun i => a.start memory (regs i)) words indices final)
    (compatible : Concurrent.Visibility.Compatible (fun space => match space with | .global => memory | .shared => fun _ => 0) words wordSource)
    (indexCompatible : IndexSources.Compatible memory words indices indexSource)
    (tables : a.RowsEncoded memory (nodeRows v (MeshRows.locations mesh)))
    (separated : a.InputSeparation) (done : ∀ i, (final i).halted=true)
    (cells : ∀ element i j, a.elementValue memory (element.val*(w*w)+i.val*w+j.val)=
      Correspondence.entries (localAction b d weight (matrix (gathered mesh input element))) i j)
    (boundary : Fin v → Bool)
    (flags : ∀ i, (read32 memory (a.base.toNat+a.boundary.toNat+i.val*4)≠0) ↔ boundary i=true)
    (node : Fin v) :
    decode (read64 (Concurrent.GlobalPublication.publish memory words) (Snapshot.address a node))=
      zeroBoundary boundary (tensorOperator mesh b d weight input) node := by
  rw [a.parallel_operator mesh b d weight input run compatible indexCompatible tables separated done cells node]
  simp only [true_and,flags,zeroBoundary]

end PtxTorchLean.Poisson.PTX.Assembly

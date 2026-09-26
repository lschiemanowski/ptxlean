import PtxBinary32.GridDenseBackwardLayout
import PtxBinary32.GridReplay

/-! All five actual instruction stages, including padded physical pointwise
storage. These software regression checks supplement, not replace, the proofs. -/
namespace Ptx.Scalar.Parallel.GridDenseBackward.Checks
private def seeds (_ : Fin count) : Scalar.State := ⟨97,fun _ => 0xdeadbeef,fun _ => 123,fun _ => true,[]⟩

private def execute (cfg : Grid.Config width) (program : List Instr) (start : Grid.State groups width) : IO (List Word) := do
  let threads := (List.finRange groups).flatMap (fun g => (List.finRange width).map (fun t => (g,t)))
  let schedule := (List.range program.length).flatMap (fun _ => threads)
  let result := Grid.Reference.run cfg program start schedule
  let replayed := match Grid.Replay.trace (Grid.Replay.arrays start) result.2.1 with
    | none => false
    | some a => a.global == result.1.global && (List.finRange groups).all (fun g => a.shared g == (result.1.blocks g).shared)
  let statuses := result.2.2.all (fun status => match status with
    | .advanced | .waiting | .released | .halted => true
    | _ => false)
  if !replayed || !statuses || !threads.all (fun gt => ((result.1.blocks gt.1).lanes gt.2).halted) then
    throw (IO.userError "grid backward stage failed completion, status or replay")
  return result.1.global

private def denseRun (s : Dense.Shape) (bounds : 0<s.rows → GridDense.Bounds s) (memory : List Word) : IO (List Word) := do
  if h : s.rows=0 then return memory
  else execute (GridDense.config s (bounds (by omega))) (Dense.Compact.program s) (GridDense.initial s memory seeds)

private def pointwiseRun (op : Pointwise.Op) (l : Pointwise.Layout n) (memory : List Word)
    (margin : l.prefixWords+n+32<2^30) : IO (List Word) := do
  if h : n=0 then return memory
  else
    let nonemptyPrefix : 0<l.prefixWords := by have := l.leftBound ⟨0,by omega⟩; omega
    let small : l.prefixWords+GridPointwise.groupCount n 32*32<2^30 := by
      have := GridPointwise.capacity_bounds n 32 (by decide); omega
    let physical := GridPointwise.paddedLayout l 32 (by decide) nonemptyPrefix small
    let final ← execute ⟨⟨94,70⟩,by decide,by decide⟩ (Pointwise.program op)
      (GridPointwise.initial physical (GridPointwise.extend l 32 memory) seeds)
    return final.take memory.length

private def check (label : String) (s : Shape) (b : Bounds s)
    (inputs : List Word) (incoming : Fin s.rows → Word) (expectedG expectedW expectedX : List Word) : IO Unit := do
  if inputs.length != s.forward.outputBase then throw (IO.userError "invalid input fixture")
  let memory := inputs ++ List.replicate s.rows 0
  let forward ← denseRun s.forward b.forward memory
  let gated ← pointwiseRun .gate (gateLayout s b) (gateInput s forward incoming) (by have := b.small; dsimp [gateLayout,DenseBackward.Shape.copyBase,DenseBackward.Shape.weightBase] at *; omega)
  let weighted ← pointwiseRun .mul (weightLayout s b) (weightInput s gated) (by have := b.small; dsimp [weightLayout,DenseBackward.Shape.copyBase] at *; omega)
  let copied ← pointwiseRun .copy (copyLayout s b) (copyInput s weighted) b.small
  let dx ← denseRun s.transposed b.transposed (packet s copied)
  let gotG := (gated.drop s.gateBase).take s.rows
  let gotW := (weighted.drop s.weightBase).take s.weightCount
  let gotX := (dx.drop s.transposed.outputBase).take s.columns
  if gotG != expectedG || gotW != expectedW || gotX != expectedX || weighted.take s.forward.outputBase != inputs then
    throw (IO.userError s!"{label}: db={gotG.map BitVec.toNat}, dW={gotW.map BitVec.toNat}, dx={gotX.map BitVec.toNat}")
  IO.println s!"Grid backward interpreter check passed: {label}"

private theorem small_bounds (s : Shape)
    (f : 0<s.rows → GridDense.Bounds s.forward) (t : 0<s.columns → GridDense.Bounds s.transposed)
    (a : s.copyBase+s.transposed.globalWords+32<2^30) : Bounds s := ⟨f,t,a⟩

def run : IO Unit := do
  check "padded columns and inactive row" ⟨⟨2,3,2,by decide,true⟩,rfl,1,by decide⟩
    (by apply small_bounds <;> intros <;> first | (constructor <;> first | (constructor <;> decide) | decide) | decide)
    [0x3f800000,0x40000000,0x40400000,0x3f800000,0x40000000,0x40400000,
      0xbf800000,0xc0000000,0xc0400000,0x3f800000,0x3f800000]
    (fun r => if r.val=0 then 0x40000000 else 0x40e00000)
    [0x40000000,0] [0x40000000,0x40800000,0x40c00000,0,0,0] [0x40000000,0x40800000,0x40c00000]
  check "padded rows and negative input gradients" ⟨⟨3,2,1,by decide,true⟩,rfl,2,by decide⟩
    (by apply small_bounds <;> intros <;> first | (constructor <;> first | (constructor <;> decide) | decide) | decide)
    [0x3f800000,0xc0000000,0x3f800000,0,0,0x3f800000,0xbf800000,0xbf800000,0,0x40400000,0]
    (fun r => if r.val=0 then 0x40000000 else if r.val=1 then 0xc0400000 else 0x40800000)
    [0x40000000,0xc0400000,0x40800000]
    [0x40000000,0xc0800000,0xc0400000,0x40c00000,0x40800000,0xc1000000]
    [0xc0000000,0xc0e00000]
  check "empty input dimension" ⟨⟨2,0,0,by decide,true⟩,rfl,1,by decide⟩
    (by apply small_bounds <;> intros <;> first | (constructor <;> first | (constructor <;> decide) | decide) | decide | omega)
    [0x40000000,0xbf800000] (fun r => if r.val=0 then 0x40400000 else 0x40a00000)
    [0x40400000,0] [] []
  check "empty output dimension" ⟨⟨0,3,2,by decide,true⟩,rfl,0,by decide⟩
    (by apply small_bounds <;> intros <;> first | (constructor <;> first | (constructor <;> decide) | decide) | decide | omega)
    [0x3f800000,0x40000000,0x40400000] (fun r => Fin.elim0 r) [] [] [0,0,0]
  check "both dimensions empty" ⟨⟨0,0,0,by decide,true⟩,rfl,0,by decide⟩
    (by apply small_bounds <;> intros <;> first | (constructor <;> first | (constructor <;> decide) | decide) | decide | omega)
    [] (fun r => Fin.elim0 r) [] [] []
  check "zero activation follows the zero convention" ⟨⟨1,1,0,by decide,true⟩,rfl,0,by decide⟩
    (by apply small_bounds <;> intros <;> first | (constructor <;> first | (constructor <;> decide) | decide) | decide)
    [0x40000000,0xbf800000,0x40000000] (fun _ => 0x40e00000) [0] [0] [0]

  check "33 by 32: both reductions and pointwise work span more than 1024 total lanes"
    ⟨⟨33,32,5,by decide,true⟩,rfl,6,by decide⟩
    (by apply small_bounds <;> intros <;> first | (constructor <;> first | (constructor <;> decide) | decide) | decide)
    (List.replicate (32+33*32) 0x3f800000 ++ List.replicate 33 0)
    (fun _ => 0x3f800000) (List.replicate 33 0x3f800000)
    (List.replicate (33*32) 0x3f800000) (List.replicate 32 0x42040000)

/-- Arbitrary words, not the interpreter fixture: the larger launch's storage
and resource assumptions suffice to instantiate the general existence theorem. -/
theorem large_execution_exists (before : List Word) (incoming : Fin 33 → Word)
    (size : before.length=1154) :
    let s : Shape := ⟨⟨33,32,5,by decide,true⟩,rfl,6,by decide⟩
    ∃ b : Bounds s, Nonempty (Execution s b before incoming) := by
  dsimp
  let b : Bounds (⟨⟨33,32,5,by decide,true⟩,rfl,6,by decide⟩ : Shape) :=
    ⟨fun _ => ⟨⟨by decide,by decide⟩,by decide⟩,
      fun _ => ⟨⟨by decide,by decide⟩,by decide⟩,by decide⟩
  exact ⟨b,execution_exists _ b before incoming size⟩

#eval run
end Ptx.Scalar.Parallel.GridDenseBackward.Checks

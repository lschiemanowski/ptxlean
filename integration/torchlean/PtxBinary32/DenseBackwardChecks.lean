import PtxBinary32.DenseBackwardLayout
import PtxBinary32.DenseChecks

/-! Software regression checks only: no GPU run, benchmark or proof by evaluation.
These execute all five actual instruction lists and check trace replay. -/
namespace Ptx.Scalar.Parallel.DenseBackward.Checks

private def denseRun (s : Dense.Shape) (bounds : 0<s.rows → Dense.Bounds s) (memory : List Word) : IO (List Word) := do
  if h : s.rows=0 then return memory
  else
    let cfg := Dense.config s (bounds (by omega))
    let shared := List.replicate s.sharedWords 0
    let result := Reference.run cfg (Dense.program s) (Dense.initial s memory shared Dense.Checks.seeds) (Dense.Checks.schedule s)
    if !(List.finRange s.threads).all (fun t => (result.1.lanes t).halted) ||
        Replay.trace ⟨memory,shared⟩ result.2.1 != some (Replay.arrays result.1) then
      throw (IO.userError "dense backward stage failed completion or replay")
    return result.1.global

private def pointwiseRun (op : Pointwise.Op) (l : Pointwise.Layout n) (memory : List Word) : IO (List Word) := do
  if h : n=0 then return memory
  else
    let cfg := Pointwise.config (by omega : 0<n)
    let schedule := (List.finRange n).flatMap (List.replicate (Pointwise.program op).length)
    let result := Reference.run cfg (Pointwise.program op) (Pointwise.initial l memory [] Dense.Checks.seeds) schedule
    if !(List.finRange n).all (fun t => (result.1.lanes t).halted) ||
        Replay.trace ⟨memory,[]⟩ result.2.1 != some (Replay.arrays result.1) then
      throw (IO.userError "pointwise backward stage failed completion or replay")
    return result.1.global

private def check (label : String) (s : Shape) (b : Bounds s)
    (inputs : List Word) (incoming : Fin s.rows → Word) (expectedG expectedW expectedX : List Word) : IO Unit := do
  if inputs.length != s.forward.outputBase then throw (IO.userError "invalid input fixture")
  let memory := inputs ++ List.replicate s.rows 0
  let forward ← denseRun s.forward b.forward memory
  let gated ← pointwiseRun .gate (gateLayout s b) (gateInput s forward incoming)
  let weighted ← pointwiseRun .mul (weightLayout s b) (weightInput s gated)
  let copied ← pointwiseRun .copy (copyLayout s b) (copyInput s weighted)
  let dx ← denseRun s.transposed b.transposed (packet s copied)
  let gotG := (gated.drop s.gateBase).take s.rows
  let gotW := (weighted.drop s.weightBase).take s.weightCount
  let gotX := (dx.drop s.transposed.outputBase).take s.columns
  if gotG != expectedG || gotW != expectedW || gotX != expectedX || weighted.take s.forward.outputBase != inputs then
    throw (IO.userError s!"{label}: db={gotG.map BitVec.toNat}, dW={gotW.map BitVec.toNat}, dx={gotX.map BitVec.toNat}")
  IO.println s!"Dense backward interpreter check passed: {label}"

private theorem small_bounds (s : Shape)
    (f : 0<s.rows → Dense.Bounds s.forward) (t : 0<s.columns → Dense.Bounds s.transposed)
    (c : s.transposed.globalWords≤1024) (a : s.copyBase+s.transposed.globalWords<2^30) : Bounds s := ⟨f,t,c,a⟩

def run : IO Unit := do
  check "padded columns and inactive row" ⟨⟨2,3,2,by decide,true⟩,rfl,1,by decide⟩
    (by apply small_bounds <;> intros <;> first | (constructor <;> decide) | decide)
    [0x3f800000,0x40000000,0x40400000,0x3f800000,0x40000000,0x40400000,
      0xbf800000,0xc0000000,0xc0400000,0x3f800000,0x3f800000]
    (fun r => if r.val=0 then 0x40000000 else 0x40e00000)
    [0x40000000,0] [0x40000000,0x40800000,0x40c00000,0,0,0] [0x40000000,0x40800000,0x40c00000]
  check "padded rows and negative input gradients" ⟨⟨3,2,1,by decide,true⟩,rfl,2,by decide⟩
    (by apply small_bounds <;> intros <;> first | (constructor <;> decide) | decide)
    [0x3f800000,0xc0000000,0x3f800000,0,0,0x3f800000,0xbf800000,0xbf800000,0,0x40400000,0]
    (fun r => if r.val=0 then 0x40000000 else if r.val=1 then 0xc0400000 else 0x40800000)
    [0x40000000,0xc0400000,0x40800000]
    [0x40000000,0xc0800000,0xc0400000,0x40c00000,0x40800000,0xc1000000]
    [0xc0000000,0xc0e00000]
  check "empty input dimension" ⟨⟨2,0,0,by decide,true⟩,rfl,1,by decide⟩
    (by apply small_bounds <;> intros <;> first | (constructor <;> first | assumption | decide) | decide | omega)
    [0x40000000,0xbf800000] (fun r => if r.val=0 then 0x40400000 else 0x40a00000)
    [0x40400000,0] [] []
  check "empty output dimension" ⟨⟨0,3,2,by decide,true⟩,rfl,0,by decide⟩
    (by apply small_bounds <;> intros <;> first | (constructor <;> first | assumption | decide) | decide | omega)
    [0x3f800000,0x40000000,0x40400000] (fun r => Fin.elim0 r) [] [] [0,0,0]
  check "both dimensions empty" ⟨⟨0,0,0,by decide,true⟩,rfl,0,by decide⟩
    (by apply small_bounds <;> intros <;> first | (constructor <;> first | assumption | decide) | decide | omega)
    [] (fun r => Fin.elim0 r) [] [] []
  check "zero activation follows the zero convention" ⟨⟨1,1,0,by decide,true⟩,rfl,0,by decide⟩
    (by apply small_bounds <;> intros <;> first | (constructor <;> decide) | decide)
    [0x40000000,0xbf800000,0x40000000] (fun _ => 0x40e00000) [0] [0] [0]

#eval run
end Ptx.Scalar.Parallel.DenseBackward.Checks

import PtxBinary32.GridReference
import PtxBinary32.GridPointwisePadding

/-! Executable software checks of actual grid interleavings. These are regression
checks, not proofs of numerical accuracy, admission, or GPU behavior. -/
namespace Ptx.Scalar.Parallel.Grid.Checks

private def cfg (n : Nat) (pos : 0<n) (cap : n≤1024) : Config n := ⟨⟨94,70⟩,pos,cap⟩
private def seeds (_ : Fin count) : Scalar.State := ⟨97,fun _ => 0xdeadbeef,fun _ => 123,fun _ => true,[]⟩

private def pointwise (label : String) (groups width : Nat) (pos : 0<width) (cap : width≤1024)
    (l : GridPointwise.Layout groups width) (op : Pointwise.Op) (before expected : List Word) : IO Unit := do
  let start := GridPointwise.initial l before seeds
  let threads := (List.finRange groups).flatMap (fun g => (List.finRange width).map (fun t => (g,t)))
  let schedule := (List.range (Pointwise.program op).length).flatMap (fun _ => threads)
  let result := Reference.run (cfg width pos cap) (Pointwise.program op) start schedule
  if result.1.global != expected || !threads.all (fun gt => ((result.1.blocks gt.1).lanes gt.2).halted) then
    throw (IO.userError s!"grid pointwise regression failed: {label}")
  IO.println s!"Grid interpreter check passed: {label}"

private def products (groups width : Nat) (small : 2+groups*width<2^30) : GridPointwise.Layout groups width :=
  ⟨2,fun t => (t.val/2)%2,fun t => t.val%2,fun _ => Nat.mod_lt _ (by decide),fun _ => Nat.mod_lt _ (by decide),small⟩

private def privateStart : State 2 2 :=
  ⟨[0,0,0,0],fun g => ⟨fun t => ⟨⟨0,fun _ => 0,fun a => if a=0 then 0 else BitVec.ofNat 64 (4*(g.val*2+t.val)),fun _ => false,[]⟩,false⟩,
    [if g.val=0 then 7 else 11],Barrier.reset 0,none⟩⟩
private def privateProgram : List Instr := [
  .memory .shared (.plain (.load 4 (.reg 0))),.sync 0,
  .memory .global (.plain (.store (.reg 1) (.reg 4))),.exit]

private def privateCheck : IO Unit := do
  let g0 : Fin 2 := 0
  let g1 : Fin 2 := 1
  let group0 := (List.range 4).flatMap (fun _ => (List.finRange 2).map (fun t => (g0,t)))
  let first := Reference.run (cfg 2 (by decide) (by decide)) privateProgram privateStart group0
  if first.1.global != [7,7,0,0] || (first.1.blocks g0).barrier.generation != 1 ||
      (first.1.blocks g1).barrier.generation != 0 || !(List.finRange 2).all (fun t => ((first.1.blocks g0).lanes t).halted) then
    throw (IO.userError "one group's barrier did not remain private")
  let group1 := (List.range 4).flatMap (fun _ => (List.finRange 2).map (fun t => (g1,t)))
  let second := Reference.run (cfg 2 (by decide) (by decide)) privateProgram first.1 group1
  if second.1.global != [7,7,11,11] then throw (IO.userError "shared addresses did not remain private")
  IO.println "Grid interpreter check passed: private scratch and independent barriers"

def run : IO Unit := do
  pointwise "interleaved multiplication" 2 2 (by decide) (by decide) (products 2 2 (by decide)) .mul
    [0x40000000,0x40400000,0,0,0,0] [0x40000000,0x40400000,0x40800000,0x40c00000,0x40c00000,0x41100000]
  pointwise "interleaved copy" 2 2 (by decide) (by decide) (products 2 2 (by decide)) .copy
    [7,11,0,0,0,0] [7,11,7,11,7,11]
  pointwise "positive and zero gates" 2 2 (by decide) (by decide) (products 2 2 (by decide)) .gate
    [0x3f800000,0,0,0,0,0] [0x3f800000,0,0x3f800000,0,0,0]
  pointwise "more than 1024 total threads" 65 32 (by decide) (by decide) (products 65 32 (by decide)) .mul
    ([0x3f800000,0x3f800000]++List.replicate (65*32) 0) (List.replicate (2+65*32) 0x3f800000)
  pointwise "empty grid" 0 32 (by decide) (by decide) (products 0 32 (by decide)) .mul [7,11] [7,11]
  let logical : Pointwise.Layout 3 := ⟨2,fun _ => 0,fun _ => 1,by decide,by decide,by decide⟩
  pointwise "partial final group with allocated padding" 2 2 (by decide) (by decide)
    (GridPointwise.paddedLayout logical 2 (by decide) (by decide) (by decide)) .copy
    [7,11,0,0,0,0] [7,11,11,11,11,7]
  privateCheck

#eval run
end Ptx.Scalar.Parallel.Grid.Checks

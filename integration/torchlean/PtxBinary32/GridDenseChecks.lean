import PtxBinary32.GridReference
import PtxBinary32.GridDenseProgram

/-! Software regressions, not graph admission or execution-existence proofs. -/
namespace Ptx.Scalar.Parallel.GridDense.Checks
private def seeds (_ : Fin count) : Scalar.State := ⟨123,fun _ => 0xdeadbeef,fun _ => 0xffffffffffffffff,fun _ => true,[]⟩

def check (name : String) (s : Dense.Shape) (bounds : Bounds s) (input expected : List Word) (serialGroups : Bool := false) : IO Unit := do
  if input.length != s.outputBase || expected.length != s.rows then throw (IO.userError "bad grid fixture")
  let global := input++List.replicate s.rows 0xdeadbeef
  let threads := (List.finRange s.rows).flatMap (fun g => (List.finRange s.width).map (fun t => (g,t)))
  let schedule := if serialGroups then
      (List.finRange s.rows).flatMap (fun g => (List.range (Dense.Compact.program s).length).flatMap
        (fun _ => (List.finRange s.width).map (fun t => (g,t))))
    else (List.range (Dense.Compact.program s).length).flatMap (fun _ => threads)
  let result := Grid.Reference.run (config s bounds) (Dense.Compact.program s) (initial s global seeds) schedule
  let statuses := result.2.2.all fun status => match status with
    | .advanced | .waiting | .released | .halted => true
    | _ => false
  let done := threads.all (fun gt => ((result.1.blocks gt.1).lanes gt.2).halted)
  if !statuses || !done || result.1.global.drop s.outputBase != expected ||
      result.1.global.take s.outputBase != input || result.1.global.length != global.length ||
      !(List.finRange s.rows).all (fun g => (result.1.blocks g).shared.length == Dense.Compact.sharedWords s &&
        (result.1.blocks g).barrier.generation == s.depth+1) then
    throw (IO.userError s!"grid dense regression failed: {name}")
  IO.println s!"Grid dense interpreter check passed: {name}"

def run : IO Unit := do
  let compact : Dense.Shape := ⟨33,32,5,by decide,true⟩
  let memory := initial compact [] seeds
  if compact.sharedWords != 6336 ||
      !(List.finRange 33).all (fun g => (memory.blocks g).shared.length == 192) then
    throw (IO.userError "compact scratch allocation regression")
  IO.println "Compact allocation check passed: 192 words per group for 33 by 32"

  let s : Dense.Shape := ⟨2,3,2,by decide,true⟩
  let bounds : Bounds s := ⟨⟨by decide,by decide⟩,by decide⟩
  let input := [0x3f800000,0x40000000,0x40400000,
     0x3f800000,0x40000000,0x40400000,0xbf800000,0xc0000000,0xc0400000,
     0x3f800000,0x3f800000]
  check "interleaved row groups and padded columns" s bounds input [0x41700000,0]
  check "one row group finishes before the other starts" s bounds input [0x41700000,0] true
  check "empty input" ⟨2,0,0,by decide,true⟩ ⟨⟨by decide,by decide⟩,by decide⟩ [0x40000000,0xbf800000] [0x40000000,0]
  check "empty output" ⟨0,2,1,by decide,true⟩ ⟨⟨by decide,by decide⟩,by decide⟩ [7,11] []
  check "affine reduction preserves negative outputs" ⟨2,0,0,by decide,false⟩ ⟨⟨by decide,by decide⟩,by decide⟩ [0x40000000,0xbf800000] [0x40000000,0xbf800000]
  check "1056 total threads in 33 independent rows" ⟨33,0,5,by decide,true⟩ ⟨⟨by decide,by decide⟩,by decide⟩ (List.replicate 33 0x3f800000) (List.replicate 33 0x3f800000)

#eval run
end Ptx.Scalar.Parallel.GridDense.Checks

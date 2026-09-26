import PtxBinary32.DenseProgram
import PtxBinary32.ParallelReplay

/-! Executable regression checks of the selected software interpreter. These
exercise the entire instruction list, but are tests, not general correctness
or memory-admission proofs. No GPU program or benchmark is run. -/
namespace Ptx.Scalar.Parallel.Dense.Checks

/-- Run every lane's straight-line segment, then all barrier arrivals. -/
def schedule (s : Shape) : List (Fin s.threads) :=
  let lanes := List.finRange s.threads
  let segment := fun count => lanes.flatMap (List.replicate count)
  segment 21 ++ lanes ++
    (List.replicate s.depth (segment 15 ++ lanes)).flatten ++ segment 20

/-- Sentinel registers ensure the tests do not accidentally rely on zeroed
caller state. The kernel initializes its own working operands and predicates. -/
def seeds (t : Fin n) : Scalar.State :=
  ⟨123,fun _ => BitVec.ofNat 32 (0xdeadbeef+t.val),fun _ => BitVec.ofNat 64 0xffffffffffffffff,
    fun _ => true,[BitVec.ofNat 32 0xdeadbeef]⟩

def check (label : String) (s : Shape) (b : Bounds s)
    (input expected : List Word) : IO Unit := do
  if input.length != s.outputBase || expected.length != s.rows then
    throw (IO.userError s!"{label}: invalid test fixture")
  let global := input ++ List.replicate s.rows (BitVec.ofNat 32 0xdeadbeef)
  let shared := List.replicate s.sharedWords (BitVec.ofNat 32 0xdeadbeef)
  let result := Reference.run (config s b) (program s) (initial s global shared seeds) (schedule s)
  let statuses := result.2.2.all fun status => match status with
    | .advanced | .waiting | .released | .halted => true
    | _ => false
  let completed := (List.finRange s.threads).all fun t =>
    (result.1.lanes t).halted && (result.1.lanes t).scalar.pc == (program s).length-1
  let outputs := (result.1.global.drop s.outputBase).take s.rows
  if !statuses || !completed || outputs != expected || result.1.global.take s.outputBase != input ||
      result.1.global.length != global.length || result.1.shared.length != shared.length ||
      result.1.barrier.generation != s.depth+1 ||
      Replay.trace ⟨global,shared⟩ result.2.1 != some (Replay.arrays result.1) then
    throw (IO.userError s!"{label}: interpreter regression; outputs {outputs.map BitVec.toNat}")
  IO.println s!"Dense interpreter check passed: {label}"

def run : IO Unit := do
  -- x=(1,2,3); rows (1,2,3),(-1,-2,-3); biases (1,1).
  check "two rows, three inputs, padded width four" ⟨2,3,2,by decide,true⟩
    (by constructor <;> decide)
    [0x3f800000,0x40000000,0x40400000,
     0x3f800000,0x40000000,0x40400000,0xbf800000,0xc0000000,0xc0400000,
     0x3f800000,0x3f800000] [0x41700000,0]
  check "empty input, two biases" ⟨2,0,0,by decide,true⟩
    (by constructor <;> decide) [0x40000000,0xbf800000] [0x40000000,0]
  check "one input, activation exactly zero" ⟨1,1,0,by decide,true⟩
    (by constructor <;> decide) [0x40000000,0xbf800000,0x40000000] [0]
  check "two rows, power-of-two width" ⟨2,2,1,by decide,true⟩
    (by constructor <;> decide)
    [0x40400000,0x40800000,0x3f800000,0,0,0x3f800000,0,0xc0a00000] [0x40400000,0]

#eval run

end Ptx.Scalar.Parallel.Dense.Checks

import Ptx.FunnelRotation
open Ptx Ptx.Scalar

-- Register interface: r0 = input/output word, r1 = unsigned runtime count.
-- Every other register and the entire memory are arbitrary and preserved.
private def input (count : Word) : State :=
  ⟨0, fun r => if r = 0 then 0x12345678 else if r = 1 then count else 99,
   fun _ => 0, fun _ => false, [17, 23]⟩

-- Execute the instruction computation, rather than evaluating the specification.
#eval ((FunnelRotation.execute true (input 8)).regs 0).toNat   -- 878082066 = 0x34567812
#eval ((FunnelRotation.execute false (input 8)).regs 0).toNat  -- 2014458966 = 0x78123456
#eval ((FunnelRotation.execute true (input 40)).regs 0).toNat  -- same as count 8
#eval ((FunnelRotation.execute true (input 32)).regs 0).toNat  -- 305419896 = original
#eval (FunnelRotation.execute true (input 8)).memory.map BitVec.toNat -- [17, 23]

-- Lean checks these universal proofs, not just the calculations above.
#check FunnelRotation.compute_rotation
#check FunnelRotation.execution_exists
#check FunnelRotation.correct
#check FunnelRotation.frame
#check FunnelRotation.no_memory_access
#check FunnelRotation.repeated_reads

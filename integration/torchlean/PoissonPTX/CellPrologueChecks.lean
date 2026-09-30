import PoissonPTX.CellPrologueEntry

namespace PtxTorchLean.Poisson.PTX.CellPrologue.Checks
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-- Deliberately nonzero, unrelated initial registers and memory. -/
def start : State := ⟨⟨0,fun _ => 0xffffffffffffffff,fun _ => 0xa5,fun _ => 0x5a,
  4096,4096,256,1400⟩,true⟩

def ctx (lane : Nat) : Context := ⟨4096,256,BitVec.ofNat 32 lane,37⟩

/-- Check every active and padding lane of Q1--Q4. -/
theorem all_lanes : ∀ w : Fin 4, ∀ lane : Fin 32,
    (execute (ctx lane.val) (program (w.val+2)) 7 start).map
      (fun s => (s.core.pc,[s.core.regs 0,s.core.regs 3,s.core.regs 14,s.core.regs 15,
        s.core.regs 16,s.core.regs 17,s.core.regs 11],s.live,[s.core.global 4100,s.core.shared 260]))=
    some (7,[4096,256,BitVec.ofNat 64 lane.val,37,
      BitVec.ofNat 64 (lane.val/(w.val+2)),BitVec.ofNat 64 (lane.val%(w.val+2)),
      0xffffffffffffffff],decide (lane.val<(w.val+2)*(w.val+2)),[0xa5,0x5a]) := by decide +kernel

theorem zero_width_unsupported : execute (ctx 5) (program 0) 7 start=none := by decide +kernel

theorem wrong_pc_rejected : execute (ctx 5) (program 3) 7
    {start with core:={start.core with pc:=1}}=none := by decide +kernel

/-- A remainder in the row slot does not satisfy the required row contract. -/
theorem row_mutation_rejected :
    (execute (ctx 5) ((program 3).set 5 (.rem32 16 14 3)) 7 start).map
      (fun s => s.core.regs 16)≠some (BitVec.ofNat 64 (5/3)) := by decide +kernel

/-- The predicate boundary includes exactly width squared lanes. -/
theorem wrong_guard_rejected :
    (execute (ctx 9) ((program 3).set 4 (.lt32 14 10)) 7 start).map
      (fun s => s.live)=some true ∧
    (execute (ctx 9) (program 3) 7 start).map (fun s => s.live)=some false := by decide +kernel

theorem high_unsigned_lane :
    (execute (ctx (2^32-1)) (program 5) 7 start).map
      (fun s => (s.core.regs 16,s.core.regs 17,s.live))=
    some (858993459,0,false) := by decide +kernel

end PtxTorchLean.Poisson.PTX.CellPrologue.Checks

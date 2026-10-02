import PoissonPTX.CellGatherLayout

namespace PtxTorchLean.Poisson.PTX.CellGather.Checks
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

/-- Nonzero arena/shared bases, cell one/lane two, and adjacent connectivity
entry containing all ones. The gather must read only its own four bytes. -/
def start (bits : Word) : State where
  pc := 0
  regs := fun r => if r=0 then 4096 else if r=3 then 256 else if r=15 then 1 else
    if r=14 then 2 else if r=16 then 1 else if r=17 then 0 else 0xaaaaaaaaaaaaaaaa
  global := write64 (write32 (write32 (fun _ => 0) 4120 2) 4124 0xffffffff) 4176 bits
  shared := fun _ => 0x5a
  globalStart := 4096
  globalBytes := 512
  sharedStart := 256
  sharedBytes := 224

/-- The chosen index is 1*4+2, so byte offsets are 24, 64+2*8, and 2*8. -/
theorem addresses :
    (connectivityAddress (start 0) 2 0).toNat=4120 ∧ node (start 0) 2 0=2 ∧
    (sourceAddress (start 0) 2 0 64).toNat=4176 ∧ (destination (start 0)).toNat=272 := by decide +kernel

theorem bits_copied : ∀ choice : Fin 3,
    let bits : Word := if choice.val=0 then 0x8000000000000000 else
      if choice.val=1 then 0x7ff8000000000042 else 0x3ff0000000000000
    (Indexed.run (code 2 0 64) (start bits)).map
      (fun s => (s.pc,[read64 s.shared 272,s.regs 18,s.regs 16,s.regs 17],[s.shared 271,s.shared 280]))=
    some (12,[bits,2,1,0],[0x5a,0x5a]) := by decide +kernel

/-- An index load needs only four allocated bytes, with four-byte alignment. -/
theorem four_byte_extent :
    Valid32 4 4 4 ∧ ¬Valid64 4 4 4 ∧
    (Indexed.eval (.load32 18 2) {(start 0) with regs:=fun _ => 4, globalStart:=4,globalBytes:=4}).isSome=true := by decide +kernel

theorem unaligned_rejected :
    Indexed.eval (.load32 18 2) {(start 0) with regs:=fun _ => 4097}=none := by decide +kernel

theorem truncated_index_rejected :
    Indexed.eval (.load32 18 2) {(start 0) with regs:=fun _ => 4096,globalBytes:=3}=none := by decide +kernel

theorem invalid_node_rejected :
    (Indexed.run (code 2 0 64) {(start 0) with global:=write32 (start 0).global 4120 0xffffffff})=none := by decide +kernel

theorem neighboring_index : read32 (write32 (write32 (fun _ => 0) 4 2) 8 0xffffffff) 4=2 := by decide +kernel

theorem mixed_overlap_rejected :
    read32 (write64 (write32 (fun _ => 0) 4 0xffffffff) 0 0) 4≠0xffffffff := by decide +kernel

end PtxTorchLean.Poisson.PTX.CellGather.Checks

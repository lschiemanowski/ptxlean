import PoissonPTX.AssemblyEntryExists
import PoissonPTX.Sources

namespace PtxTorchLean.Poisson.PTX.Assembly

/-- Storage and launch geometry. The size bound matches the emitted host
layout and prevents wrap in node indexing and the next-offset calculation. -/
structure Arena (nodes : Nat) where
  (base offsets entries element boundary output : Word)
  (bytes entryCount elementCount : Nat)
  small : nodes<2^30
  entriesSmall : entryCount<2^32
  aligned : base.toNat%8=0
  noWrap : base.toNat+bytes≤2^64
  offsetAligned : offsets.toNat%4=0
  entryAligned : entries.toNat%4=0
  elementAligned : element.toNat%8=0
  boundaryAligned : boundary.toNat%4=0
  outputAligned : output.toNat%8=0
  offsetsFit : offsets.toNat+(nodes+1)*4≤bytes
  entriesFit : entries.toNat+entryCount*4≤bytes
  elementFit : element.toNat+elementCount*8≤bytes
  boundaryFit : boundary.toNat+nodes*4≤bytes
  outputFit : output.toNat+nodes*8≤bytes

def Arena.context (a : Arena n) (i : Fin n) : Kernel.Context :=
  ⟨a.base,BitVec.ofNat 32 (i.val%256),BitVec.ofNat 32 (i.val/256)⟩

def Arena.start (a : Arena n) (memory : Memory) (regs : Registers) : Flow.State :=
  ⟨{pc:=0,regs:=regs,global:=memory,shared:=fun _ => 0,globalStart:=a.base.toNat,
    globalBytes:=a.bytes,sharedStart:=0,sharedBytes:=0},fun _ => false,false⟩

def Arena.offset (a : Arena n) (memory : Memory) (k : Nat) : Nat :=
  (read32 memory (a.base.toNat+a.offsets.toNat+k*4)).toNat

/-- Conditions on initial index bytes only: offset ranges are ordered and
inside the index array, and each contribution index names an allocated value. -/
structure Arena.Contents (a : Arena n) (memory : Memory) : Prop where
  ordered : ∀ i<n, a.offset memory i≤a.offset memory (i+1)
  last : ∀ i<n, a.offset memory (i+1)≤a.entryCount
  indices : ∀ k<a.entryCount,
    (read32 memory (a.base.toNat+a.entries.toNat+k*4)).toNat<a.elementCount

theorem Arena.index (a : Arena n) (i : Fin n) : (Kernel.Residual.index (a.context i)).toNat=i.val := by
  have hi:=i.isLt; have small:=a.small
  simp [Kernel.Residual.index,Arena.context,BitVec.toNat_add,BitVec.toNat_mul]
  omega

theorem Arena.live (a : Arena n) (i : Fin n) : Kernel.Residual.live (a.context i) (BitVec.ofNat 32 n) := by
  unfold Kernel.Residual.live
  rw [a.index i]
  have small : n<2^32 := by have := a.small; omega
  change i.val<n%2^32
  rw [Nat.mod_eq_of_lt small]
  exact i.isLt

theorem Arena.offset_index (a : Arena n) (i : Fin n) (next : Bool) :
    (Kernel.u32 (if next then add32 ((Kernel.Residual.index (a.context i)).setWidth 64) 1
      else (Kernel.Residual.index (a.context i)).setWidth 64)).toNat=i.val+(if next then 1 else 0) := by
  have hi:=i.isLt; have small:=a.small
  cases next <;> simp [Kernel.u32,add32,a.index,BitVec.toNat_setWidth,BitVec.toNat_add] <;> omega

theorem Arena.offset_address (a : Arena n) (memory : Memory) (regs : Registers) (i : Fin n) (next : Bool) :
    (offsetAddress (setup (a.context i) (BitVec.ofNat 32 n) (a.start memory regs)).core a.offsets next).toNat=
      a.base.toNat+a.offsets.toNat+(i.val+(if next then 1 else 0))*4 := by
  have idx := a.offset_index i next
  have narrow : i.val+(if next then 1 else 0)<n+1 := by have := i.isLt; cases next <;> simp <;> omega
  simp only [offsetAddress,setup,Function.update_apply]
  simp only [show (12:Nat)≠15 by decide,show (12:Nat)≠14 by decide,show (12:Nat)≠0 by decide,
    show (0:Nat)≠12 by decide,show (0:Nat)≠15 by decide,show (0:Nat)≠14 by decide,ite_true,ite_false]
  change (address32 a.base _ a.offsets).toNat=_
  rw [address32_exact _ _ _ (by rw [idx]; have := a.offsetsFit; have := a.noWrap; omega),idx]
  omega

theorem Arena.prepare_valid (a : Arena n) (memory : Memory) (regs : Registers) (i : Fin n) :
    PrepareValid (setup (a.context i) (BitVec.ofNat 32 n) (a.start memory regs)).core a.offsets := by
  constructor <;> rw [a.offset_address]
  all_goals
    change Valid32 a.base.toNat a.bytes _
    refine ⟨by omega,?_,?_,a.noWrap⟩
    · have base4 : a.base.toNat%4=0 := by have := a.aligned; omega
      simp [Nat.add_mod,base4,a.offsetAligned]
    · have := a.offsetsFit; have := i.isLt; simp; omega

theorem Arena.ready_cursor (a : Arena n) (memory : Memory) (regs : Registers) (i : Fin n) :
    cursor (ready (a.context i) (BitVec.ofNat 32 n) a.offsets (a.start memory regs)).core=a.offset memory i.val := by
  simp only [cursor,ready,prepared,Function.update_apply]
  simp only [show (19:Nat)≠8 by decide,show (19:Nat)≠20 by decide,show (19:Nat)≠2 by decide,
    show (19:Nat)≠1 by decide,show (19:Nat)≠13 by decide,ite_true,ite_false]
  simp only [Kernel.u32,BitVec.setWidth_setWidth_of_le _ (by decide : 32≤64)]
  unfold offsetValue
  rw [a.offset_address]
  rfl

theorem Arena.ready_limit (a : Arena n) (memory : Memory) (regs : Registers) (i : Fin n) :
    limit (ready (a.context i) (BitVec.ofNat 32 n) a.offsets (a.start memory regs)).core=a.offset memory (i.val+1) := by
  simp only [limit,ready,prepared,Function.update_apply]
  simp only [show (20:Nat)≠8 by decide,ite_false,ite_true]
  simp only [Kernel.u32,BitVec.setWidth_setWidth_of_le _ (by decide : 32≤64)]
  unfold offsetValue
  rw [a.offset_address]
  rfl

end PtxTorchLean.Poisson.PTX.Assembly

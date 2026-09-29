import PoissonPTX.CellSymbolic

namespace PtxTorchLean.Poisson.PTX.Concurrent.CellMiddle.Numeric
open Ptx Symbolic Checks

/-- State immediately after the omitted gather barrier. Row/column and base
registers are launch inputs here; this is not a proof of the omitted prologue. -/
structure Launch (width : Nat) (bases : Space → Word) (start : State 32) where
  generation : Nat
  reset : start.barrier=Barrier.reset generation
  pcs : ∀ t, (start.lanes t).pc=0
  global : ∀ t, (start.lanes t).regs 0=bases .global
  shared : ∀ t, (start.lanes t).regs 3=bases .shared
  lanes : ∀ t, (start.lanes t).regs 14=BitVec.ofNat 64 t.val
  rows : ∀ t, (start.lanes t).regs 16=BitVec.ofNat 64 (t.val/width)
  cols : ∀ t, (start.lanes t).regs 17=BitVec.ofNat 64 (t.val%width)
  fits : (bases .shared).toNat+7*width*width*8≤2^64

theorem Launch.aligned (launch : Launch width bases start) : Aligned start := by
  intro t h; simp [launch.reset,Barrier.reset] at h

theorem Launch.base_nat (launch : Launch width bases start) :
    ∀ t, ((start.lanes t).regs 3).toNat=(bases .shared).toNat := by intro t; rw [launch.shared]

theorem Launch.lane_nat (launch : Launch width bases start) :
    ∀ t, ((start.lanes t).regs 14).toNat=t.val := by
  intro t; rw [launch.lanes,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by have := t.isLt; omega)]

theorem Launch.symbolic (launch : Launch width bases start) (mode : Mode) (memory : Space → Nat → Word) :
    Symbolic.Invariant mode (program width) (width*width) (fun t => seed width t.val) bases memory start := by
  intro thread live r
  rw [launch.pcs,at_zero]
  simp only [seed]
  split
  · subst r; exact launch.global thread
  · split
    · subst r; exact launch.shared thread
    · split
      · subst r; exact launch.lanes thread
      · split
        · subst r; exact launch.rows thread
        · split
          · subst r; exact launch.cols thread
          · trivial

theorem guards (width : Nat) (lo : 2≤width) (hi : width≤5) : Symbolic.Guards (program width) (width*width) := by
  intro pc count target fetch
  exact (checked_at (Checks.checked width lo hi) fetch).1

theorem access_active (launch : Launch width bases start) (lo : 2≤width) (hi : width≤5)
    (run : Runs cfg (program width) start events final) (member : Event.data thread access∈events) :
    thread.val<width*width := by
  apply Padding.access_active run launch.aligned _ (checked_boundaries (Checks.checked width lo hi)) member
  intro t inactive
  simp [launch.pcs,Padding.outside,program,code,phase]

/-- No read-value condition is needed for the actual load address. -/
theorem load_location (launch : Launch width bases start) (lo : 2≤width) (hi : width≤5)
    (run : Runs cfg (program width) start events final)
    (member : Event.data thread access∈events) (read : access.data.store=false) :
    ∃ off : Word, access.data.address=(bases access.space+off).toNat ∧ off.toNat%8=0 ∧
      (access.space=.shared → off.toNat<7*width*width*8 ∧
        ∀ p : Fin 7, off.toNat/(width*width*8)=p.val → p≠0 → boundary width (preceding p)<access.data.pc) := by
  have live := access_active launch lo hi run member
  obtain ⟨before,op,next,fetch,hd,hregs⟩ := Symbolic.access_registers run launch.aligned
    (launch.symbolic .addresses (fun _ _ => 0)) (guards width lo hi) (by intro h; cases h) member live
  obtain ⟨sp,dst,addr,rfl,space,pc,address,valid,result⟩ := load_origin hd read
  have fetch' : (program width)[access.data.pc]?=some (.data (.load64 sp dst addr)) := by rw [pc]; exact fetch
  obtain ⟨hp,_⟩ := List.getElem?_eq_some_iff.mp fetch'
  have cert := loads width lo hi ⟨thread.val,live⟩ ⟨access.data.pc,hp⟩
  simp only [loadCheck,fetch'] at cert
  have related := operand_sound hregs addr
  cases he : extract (operand (atPC .addresses (program width) (seed width thread.val) access.data.pc) addr) with
  | none => simp [he] at cert
  | some pair =>
    obtain ⟨sp',off⟩ := pair
    simp only [he] at cert
    obtain ⟨rfl,aligned,bounds⟩ := cert
    refine ⟨off,?_,aligned,?_⟩
    · rw [address,extract_sound related he,space]
    · simpa [space] using bounds

end PtxTorchLean.Poisson.PTX.Concurrent.CellMiddle.Numeric

import PoissonPTX.HostCellExists
import PoissonPTX.CellWholeStoreBounds

namespace PtxTorchLean.Poisson.PTX.Host
open Concurrent
variable {n e w : Nat} {a : Layout n e w}

/-- Cell publication changes only actual element-output bytes. The proof uses
the fetched entry, active-lane guard and output-address instructions, and does
not constrain nonexistent padding accesses. -/
theorem cell_frame (actual : CellLaunch a kind memory output) : a.Writes [.element] memory output := by
  obtain ⟨regs,final,events,indices,source,indexSource,run,done,pcs,compatible,indexCompatible,performed,rfl⟩ := actual
  intro byte outside
  apply GlobalPublication.outside
  intro owner access member global store
  obtain ⟨⟨block,event⟩,member,equal⟩ := List.mem_map.mp member
  change event=Event.data owner access at equal
  subst event
  have localMember : Event.data owner access∈CellGrid.forBlock block events := by
    simp only [CellGrid.forBlock,List.mem_filterMap]
    exact ⟨(block,.data owner access),member,by simp⟩
  have bounds (t : Fin 32) (active : t.val<w*w) :
      (BitVec.ofNat 32 block.val).toNat*(w*w)+t.val<2^32 ∧
      (a.cellBases .global).toNat+((BitVec.ofNat 32 block.val).toNat*(w*w)+t.val)*8+(a.offset .element).toNat<2^64 := by
    have valid := a.cell_output block t active
    have nowrap := a.noWrap
    exact ⟨valid.1,by dsimp only [Layout.cellBases]; omega⟩
  have sharedRoom : (a.cellBases .shared).toNat+7*w*w*8≤2^64 := by
    change (0:Nat)+7*w*w*8≤2^64
    have := a.hi; nlinarith
  have localRun : CellWhole.Runs (CellGrid.config block) a.cellBases (BitVec.ofNat 32 block.val) w
      (a.offset .cells) (a.offset kind.source) (a.offset .element) (a.cellContext block)
      (CellWhole.begin (a.cellStart memory (regs block)))
      (CellGrid.forBlock block events) (CellGrid.forBlock block indices) (final block) := CellGrid.project run block
  obtain ⟨active,address⟩ := CellWhole.global_store_active localRun
    (by intro t h; simp [CellWhole.begin,Layout.cellStart,Ptx.Barrier.reset] at h)
    (fun _ => rfl) (fun _ => rfl) a.lo a.hi sharedRoom
    (fun t _ => by rw [pcs]; omega) bounds localMember store global
  change access.data.address=a.base.toNat+((BitVec.ofNat 32 block.val).toNat*(w*w)+owner.val)*8+(a.offset .element).toNat at address
  rw [address,a.cell_index block]
  have bound := outside .element (by simp)
  change byte<a.base.toNat+(a.offset .element).toNat ∨
    a.base.toNat+(a.offset .element).toNat+e*w*w*8≤byte at bound
  have product := Nat.mul_le_mul_right (w*w) (show block.val+1≤e from block.isLt)
  simp only [Nat.add_mul,Nat.one_mul] at product
  rw [Nat.mul_assoc e w w] at bound
  omega

theorem cell_static (actual : CellLaunch a kind memory output) : a.Static memory output := by
  apply (cell_frame actual).static
  simp [Field.mutable]

end PtxTorchLean.Poisson.PTX.Host

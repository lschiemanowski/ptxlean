import PoissonPTX.CellMiddleChecks
import PoissonPTX.ConcurrentReadOnly

/-! The concrete middle slice does not write global coefficients or input plane
zero. Recovering their initial bytes requires only source compatibility. -/
namespace PtxTorchLean.Poisson.PTX.Concurrent.CellMiddle.Inputs
open Ptx
open Checks
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

/-- Finite syntax check, not a condition on an execution's numerical answer. -/
def SharedStores (code : List Instr) : Prop :=
  ∀ pc : Fin code.length, match code[pc.val] with
    | .data (.store64 sp _ _) => sp=.shared
    | _ => True

instance {code : List Instr} : Decidable (SharedStores code) := by
  unfold SharedStores
  letI : (pc : Fin code.length) → Decidable (match code[pc.val] with
    | .data (.store64 sp _ _) => sp=.shared
    | _ => True) := fun pc => by split <;> infer_instance
  exact inferInstance

theorem shared_stores (width : Nat) (lo : 2≤width) (hi : width≤5) :
    SharedStores (program width) := by
  interval_cases width <;> decide +kernel

/-- Every actual store has a fetched store instruction in shared space. -/
theorem store_space {code : List Instr} (run : Runs cfg code start events final) (checked : SharedStores code)
    (member : Event.data thread access∈events) (store : access.data.store=true) :
    access.space=.shared := by
  obtain ⟨before,earlier,selected,out,suffix,hp,hs,hm,ht,he⟩ := run_access_prefix run member
  obtain ⟨eq,op,next,fetch,hd⟩ := step_access_origin hs hm
  subst selected
  obtain ⟨sp,addr,src,he,ha,hvalid,hnext⟩ := store_origin hd store
  rw [he] at fetch
  obtain ⟨bound,atPC⟩ := List.getElem?_eq_some_iff.mp fetch
  have check := checked ⟨(before.lanes thread).pc,bound⟩
  have space : sp=.shared := by simpa [atPC] using check
  simpa [ha] using space

theorem global_readonly (width : Nat) (lo : 2≤width) (hi : width≤5)
    (run : Runs cfg (program width) start events final) (address : Nat) :
    Visibility.ReadOnly events .global address := by
  intro w writer wa observed store space j k same
  have shared := store_space run (shared_stores width lo hi) (List.mem_of_getElem? observed) store
  simp [space] at shared

/-- The sentinel site for plane zero is a guard, so it cannot have a store event. -/
theorem nonzero_plane (width : Nat) (run : Runs cfg (program width) start events final)
    (member : Event.data thread access∈events) (store : access.data.store=true)
    (pc : access.data.pc=site (program width) width plane) : plane≠0 := by
  intro eq; subst plane
  obtain ⟨before,earlier,selected,out,suffix,hp,hs,hm,ht,he⟩ := run_access_prefix run member
  obtain ⟨eq,op,next,fetch,hd⟩ := step_access_origin hs hm
  subst selected
  have apc := access_pc hd
  obtain ⟨sp,addr,src,he,ha,hvalid,hnext⟩ := store_origin hd store
  have zero : (before.lanes thread).pc=0 := by simpa [site] using apc.symm.trans pc
  rw [zero] at fetch
  simp [program,code,phase] at fetch

/-- Even a partially overlapping source is excluded: all actual stores lie
in planes 1--6, while these eight bytes lie entirely inside input plane zero. -/
theorem input_readonly {start : State 32} (width : Nat) (lo : 2≤width) (hi : width≤5)
    (run : Runs cfg (program width) start events final)
    (reset : start.barrier=Barrier.reset generation) (pcs : ∀ t, (start.lanes t).pc=0)
    (bases : ∀ t, ((start.lanes t).regs 3).toNat=base)
    (lanes : ∀ t, ((start.lanes t).regs 14).toNat=t.val)
    (fits : base+7*width*width*8≤2^64) {address : Nat}
    (_lower : base≤address) (upper : address+8≤base+width*width*8) :
    Visibility.ReadOnly events .shared address := by
  have coverage := Checks.coverage width lo hi run reset pcs bases lanes fits
  intro w writer wa observed store shared j k same
  obtain ⟨plane,active,pc,addr⟩ := coverage w writer wa observed store shared
  have positive := nonzero_plane width run (List.mem_of_getElem? observed) store pc
  have hp : 1≤plane.val := by
    have : plane.val≠0 := fun h => positive (Fin.ext h)
    omega
  have bound : width*width≤plane.val*(width*width) := Nat.le_mul_of_pos_left _ hp
  simp only [SharedPlane.address] at addr
  have hj := j.isLt; have hk := k.isLt
  have assoc : plane.val*width*width=plane.val*(width*width) := Nat.mul_assoc ..
  omega

/-- No read value is postulated: compatible sources and derived store geometry
force global/input-plane reads to the initial byte image. -/
theorem initial_value {start : State 32} {events : List (Event 32)} {index : Nat}
    (width : Nat) (lo : 2≤width) (hi : width≤5)
    (run : Runs cfg (program width) start events final)
    (reset : start.barrier=Barrier.reset generation) (pcs : ∀ t, (start.lanes t).pc=0)
    (bases : ∀ t, ((start.lanes t).regs 3).toNat=base)
    (lanes : ∀ t, ((start.lanes t).regs 14).toNat=t.val)
    (fits : base+7*width*width*8≤2^64)
    (observed : events[index]?=some (.data reader access)) (read : access.data.store=false)
    (input : access.space=.global ∨ (base≤access.data.address ∧ access.data.address+8≤base+width*width*8))
    (compatible : Visibility.Compatible initial events source) :
    access.data.value=read64 (initial access.space) access.data.address := by
  apply Visibility.read_only_value compatible observed read
  cases space : access.space with
  | global => exact global_readonly width lo hi run _
  | shared =>
    have range : base≤access.data.address ∧ access.data.address+8≤base+width*width*8 := by
      simpa [space] using input
    exact input_readonly width lo hi run reset pcs bases lanes fits range.1 range.2

end PtxTorchLean.Poisson.PTX.Concurrent.CellMiddle.Inputs

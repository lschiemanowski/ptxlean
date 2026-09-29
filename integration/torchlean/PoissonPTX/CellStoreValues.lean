import PoissonPTX.CellReadValues

namespace PtxTorchLean.Poisson.PTX.Concurrent.CellMiddle.Numeric
open Ptx Symbolic Checks

/-- An actual emitted store has the symbolic arithmetic value whenever its
reads agree with the given word view. Source justification is supplied below;
an executable fixture can instead derive its read choices directly. -/
theorem store_expression_of_reads (launch : Launch width bases start) (lo : 2≤width) (hi : width≤5)
    (run : Runs cfg (program width) start events final)
    (reads : Symbolic.Reads memory events)
    (member : Event.data thread access∈events) (store : access.data.store=true)
    (plane : Fin 7) (positive : plane≠0) (pc : access.data.pc=site (program width) width plane) :
    decode access.data.value=(expected width plane.val thread.val).eval bases memory := by
  have live := access_active launch lo hi run member
  obtain ⟨before,op,next,fetch,hd,hregs⟩ := Symbolic.access_registers run launch.aligned
    (launch.symbolic .values memory) (guards width lo hi)
    (fun _ => reads) member live
  have apc := access_pc hd
  have instruction := (Checks.stores width lo hi plane positive).1
  rw [← apc,pc,instruction] at fetch
  cases fetch
  have pv : 0<plane.val := by have h : plane.val≠0 := fun eq => positive (Fin.ext eq); omega
  let p : Fin 6 := ⟨plane.val-1,by have := plane.isLt; omega⟩
  have pe : (⟨p.val+1,by omega⟩ : Fin 7)=plane := by apply Fin.ext; dsimp [p]; omega
  have expr := Numeric.stores width lo hi ⟨thread.val,live⟩ p
  rw [pe] at expr
  have pval : p.val+1=plane.val := congrArg Fin.val pe
  rw [pval] at expr
  have result := number_sound (hregs 8) (by simpa [pc] using expr)
  cases hd with
  | store valid => exact result

/-- Source compatibility and the concrete barrier/address proof discharge
every read-value obligation for arbitrary middle-slice executions. -/
theorem store_expression (launch : Launch width bases start) (lo : 2≤width) (hi : width≤5)
    (run : Runs cfg (program width) start events final)
    (compatible : Visibility.Compatible initial events source) (performed : Visibility.Performed events source)
    (member : Event.data thread access∈events) (store : access.data.store=true)
    (plane : Fin 7) (positive : plane≠0) (pc : access.data.pc=site (program width) width plane) :
    decode access.data.value=(expected width plane.val thread.val).eval bases (view width bases initial events) :=
  store_expression_of_reads launch lo hi run (all_reads launch lo hi run compatible performed) member store plane positive pc

/-- Every output coordinate has a real producing event; no default value from
an unsuccessful store lookup is used as a substitute for execution. -/
theorem producer (launch : Launch width bases start) (lo : 2≤width) (hi : width≤5)
    (run : Runs cfg (program width) start events final)
    (done : ∀ thread, (final.lanes thread).pc=(program width).length)
    (plane : Fin 7) (positive : plane≠0) (lane : Fin (width*width)) :
    ∃ (index : Nat) (thread : Fin 32) (access : Access), thread.val=lane.val ∧
      events[index]?=some (.data thread access) ∧ access.data.pc=site (program width) width plane ∧
      access.data.store=true ∧ access.space=.shared ∧
      access.data.address=SharedPlane.address (bases .shared).toNat width plane.val lane.val := by
  have small : width*width≤25 := by nlinarith
  let thread : Fin 32 := ⟨lane.val,by have := lane.isLt; omega⟩
  have live : thread.val<width*width := lane.isLt
  obtain ⟨storeFetch,earlier⟩ := Checks.stores width lo hi plane positive
  have boundaryBound := (List.getElem?_eq_some_iff.mp (Checks.boundaries width lo hi (preceding plane)).1).1
  obtain ⟨access,member,pc,store,shared⟩ := crossed_store run launch.aligned storeFetch
    (checked_writer_stops (Checks.checked width lo hi) live) (by rw [launch.pcs]; omega)
    (by rw [done]; omega)
  obtain ⟨index,observed⟩ := List.mem_iff_getElem?.mp member
  obtain ⟨p,active,siteEq,address⟩ := Checks.coverage width lo hi run launch.reset launch.pcs
    launch.base_nat launch.lane_nat launch.fits index thread access observed store shared
  have pe : p=plane := Checks.sites_injective width lo hi (siteEq.symm.trans pc)
  subst p
  exact ⟨index,thread,access,rfl,observed,pc,store,shared,address⟩

/-- Completion forces every active producer to execute every required store.
The word view then exposes precisely that store, not a chosen numerical answer. -/
theorem plane_expression (launch : Launch width bases start) (lo : 2≤width) (hi : width≤5)
    (run : Runs cfg (program width) start events final)
    (done : ∀ thread, (final.lanes thread).pc=(program width).length)
    (compatible : Visibility.Compatible initial events source) (performed : Visibility.Performed events source)
    (plane : Fin 7) (positive : plane≠0) (lane : Fin (width*width)) :
    decode (view width bases initial events .shared
      (SharedPlane.address (bases .shared).toNat width plane.val lane.val))=
      (expected width plane.val lane.val).eval bases (view width bases initial events) := by
  have small : width*width≤25 := by nlinarith
  let thread : Fin 32 := ⟨lane.val,by have := lane.isLt; omega⟩
  have live : thread.val<width*width := lane.isLt
  obtain ⟨storeFetch,earlier⟩ := Checks.stores width lo hi plane positive
  have boundaryFetch := (Checks.boundaries width lo hi (preceding plane)).1
  have boundaryBound := (List.getElem?_eq_some_iff.mp boundaryFetch).1
  obtain ⟨access,member,pc,store,shared⟩ := crossed_store run launch.aligned storeFetch
    (checked_writer_stops (Checks.checked width lo hi) live) (by rw [launch.pcs]; omega)
    (by rw [done]; omega)
  obtain ⟨index,observed⟩ := List.mem_iff_getElem?.mp member
  have coverage := Checks.coverage width lo hi run launch.reset launch.pcs launch.base_nat launch.lane_nat launch.fits
  obtain ⟨p,active,siteEq,address⟩ := coverage index thread access observed store shared
  have pe : p=plane := Checks.sites_injective width lo hi (siteEq.symm.trans pc)
  subst p
  have owner := Checks.unique width lo hi run launch.reset launch.pcs launch.base_nat launch.lane_nat launch.fits observed store shared
  have outside := Geometry.plane_positive width thread.val (bases .shared).toNat plane positive
  rw [← address] at outside
  have word := WordView.output (initial:=initial) observed store shared owner outside
  change view width bases initial events .shared access.data.address=access.data.value at word
  rw [address] at word
  rw [word]
  exact store_expression launch lo hi run compatible performed member store plane positive pc

end PtxTorchLean.Poisson.PTX.Concurrent.CellMiddle.Numeric

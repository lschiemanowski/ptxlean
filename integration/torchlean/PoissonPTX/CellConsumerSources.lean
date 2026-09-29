import PoissonPTX.CellConsumerProgram

namespace PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer
open Ptx CellMiddle Symbolic
variable {events : List (Event 32)} {index : Nat} {access : Access} {reader thread : Fin 32}

theorem guards (width : Nat) (lo : 2≤width) (hi : width≤5) : Guards (program width) (width*width) := by
  intro pc count target fetch
  exact (checked_at (checked width lo hi) fetch).1

theorem symbolic (launch : Numeric.Launch width bases start) (mode : Mode) (memory : Space → Nat → Word) :
    Invariant mode (program width) (width*width) (fun t => Numeric.seed width t.val) bases memory start := by
  intro thread live r
  rw [launch.pcs,at_zero]
  simp only [Numeric.seed]
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

theorem coverage (launch : Numeric.Launch width bases start) (lo : 2≤width) (hi : width≤5)
    (run : Runs cfg (program width) start events final) :
    PlaneStores events (bases .shared).toNat width (site (program width) width) := by
  apply plane_stores run (checked width lo hi) launch.reset launch.pcs _ launch.base_nat launch.lane_nat hi launch.fits
  simp [Padding.outside,program,Checks.program,code,phase]

theorem unique (launch : Numeric.Launch width bases start) (lo : 2≤width) (hi : width≤5)
    (run : Runs cfg (program width) start events final)
    (observed : events[index]?=some (.data thread access))
    (store : access.data.store=true) (shared : access.space=.shared) :
    Visibility.SoleWriter events index access.data.address :=
  plane_sole_writer run (checked_forward (checked width lo hi)) (coverage launch lo hi run) observed store shared

theorem publication (launch : Numeric.Launch width bases start) (lo : 2≤width) (hi : width≤5)
    (run : Runs cfg (program width) start events final)
    (plane : Fin 7) (positive : plane≠0) (writer : Fin 32) (active : writer.val<width*width)
    (observed : events[index]?=some (.data reader access))
    (later : Checks.boundary width (Checks.preceding plane)<access.data.pc)
    (read : access.data.store=false) (shared : access.space=.shared)
    (address : access.data.address=SharedPlane.address (bases .shared).toNat width plane.val writer.val)
    (compatible : Visibility.Compatible initial events source) (performed : Visibility.Performed events source) :
    access.data.value=Numeric.view width bases initial events .shared access.data.address := by
  have injective : Function.Injective (site (program width) width) := by
    intro a b h
    apply Checks.sites_injective width lo hi
    simpa only [sites width lo hi] using h
  obtain ⟨fetch,before⟩ := stores width lo hi plane positive
  obtain ⟨barrier,stops⟩ := boundaries width lo hi (Checks.preceding plane)
  obtain ⟨w,wa,hw,pc,across,value,bytes⟩ := read_from_plane_producer run launch.reset
    (checked_forward (checked width lo hi)) (coverage launch lo hi run)
    injective plane fetch (checked_writer_stops (checked width lo hi) active)
    (by rw [launch.pcs]; omega) before barrier (Checks.bounded_stops stops)
    (by intro t; rw [launch.pcs]; omega) observed later read shared address compatible performed
  have origin := compatible index reader access observed read 0
  rw [bytes 0] at origin
  obtain ⟨actualWriter,actual,actualEvent,store,space,sameAddress,_⟩ := origin
  have eq := Option.some.inj (actualEvent.symm.trans hw)
  cases eq
  have space' : wa.space=.shared := space.trans shared
  have same : wa.data.address=access.data.address := by simpa using sameAddress
  have owner := unique launch lo hi run hw store space'
  have outside := Geometry.plane_positive width writer.val (bases .shared).toNat plane positive
  rw [← address,← same] at outside
  rw [value,← same]
  exact (WordView.output hw store space' owner outside).symm

theorem active (launch : Numeric.Launch width bases start) (lo : 2≤width) (hi : width≤5)
    (run : Runs cfg (program width) start events final) (member : Event.data thread access∈events) :
    thread.val<width*width := by
  apply Padding.access_active run launch.aligned _ (checked_boundaries (checked width lo hi)) member
  intro t inactive
  simp [launch.pcs,Padding.outside,program,Checks.program,code,phase]

/-- Final-read geometry is independent of candidate loaded values. -/
theorem load_location (launch : Numeric.Launch width bases start) (lo : 2≤width) (hi : width≤5)
    (run : Runs cfg (program width) start events final)
    (member : Event.data thread access∈events) (read : access.data.store=false)
    (late : (Checks.program width).length≤access.data.pc) :
    ∃ off : Word, access.data.address=(bases access.space+off).toNat ∧ off.toNat%8=0 ∧
      (access.space=.shared → off.toNat<7*width*width*8 ∧
        (off.toNat/(width*width*8)=5 ∨ off.toNat/(width*width*8)=6) ∧ Checks.boundary width 2<access.data.pc) := by
  have live := active launch lo hi run member
  obtain ⟨before,op,next,fetch,hd,hregs⟩ := Symbolic.access_registers run launch.aligned
    (symbolic launch .addresses (fun _ _ => 0)) (guards width lo hi) (by intro h; cases h) member live
  obtain ⟨sp,dst,addr,rfl,space,pc,address,valid,result⟩ := load_origin hd read
  have fetch' : (program width)[access.data.pc]?=some (.data (.load64 sp dst addr)) := by rw [pc]; exact fetch
  obtain ⟨hp,_⟩ := List.getElem?_eq_some_iff.mp fetch'
  have cert := loads width lo hi ⟨thread.val,live⟩ ⟨access.data.pc,hp⟩ late
  simp only [loadCheck,fetch'] at cert
  have related := operand_sound hregs addr
  cases he : Numeric.extract (operand (atPC .addresses (program width) (Numeric.seed width thread.val) access.data.pc) addr) with
  | none => simp [he] at cert
  | some pair =>
    obtain ⟨sp',off⟩ := pair
    simp only [he] at cert
    obtain ⟨rfl,aligned,bounds⟩ := cert
    refine ⟨off,?_,aligned,?_⟩
    · rw [address,Numeric.extract_sound related he,space]
    · simpa [space] using bounds

/-- Barrier history and unique actual stores determine every final load. -/
theorem load_view (launch : Numeric.Launch width bases start) (lo : 2≤width) (hi : width≤5)
    (run : Runs cfg (program width) start events final)
    (observed : events[index]?=some (.data reader access)) (read : access.data.store=false)
    (late : (Checks.program width).length≤access.data.pc)
    (compatible : Visibility.Compatible initial events source) (performed : Visibility.Performed events source) :
    access.data.value=Numeric.view width bases initial events access.space access.data.address := by
  obtain ⟨off,address,aligned,bounds⟩ := load_location launch lo hi run (List.mem_of_getElem? observed) read late
  cases space : access.space with
  | global =>
    have value := Visibility.read_only_value compatible observed read (by
      intro w writer wa hw store sameSpace j k eq
      have shared := Inputs.store_space run (shared_stores width lo hi) (List.mem_of_getElem? hw) store
      simp [sameSpace,space] at shared)
    simpa [space,Numeric.view,WordView.memory] using value
  | shared =>
    obtain ⟨bound,plane,later⟩ := bounds space
    have nowrap : (bases .shared).toNat+off.toNat<2^64 := by have h := launch.fits; omega
    have natural : access.data.address=(bases .shared).toNat+off.toNat := by
      rw [address,space,BitVec.toNat_add,Nat.mod_eq_of_lt nowrap]
    obtain ⟨p,lane,live,offset,planeIndex⟩ := Geometry.split_offset width off.toNat lo hi aligned bound
    have physical : access.data.address=SharedPlane.address (bases .shared).toNat width p.val lane.val := by
      rw [natural,offset]; rfl
    have pv : p.val=5 ∨ p.val=6 := by omega
    have positive : p≠0 := by intro h; subst p; simp at pv
    have boundary : Checks.preceding p=2 := by rcases pv with h|h <;> simp [Checks.preceding,h]
    exact publication launch lo hi run p positive lane live observed (by simpa [boundary] using later)
      read space physical compatible performed

end PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer

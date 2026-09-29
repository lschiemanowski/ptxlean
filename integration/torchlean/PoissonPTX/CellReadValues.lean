import PoissonPTX.CellLaunch
import PoissonPTX.CellReadGeometry

namespace PtxTorchLean.Poisson.PTX.Concurrent.CellMiddle.Numeric
open Ptx Symbolic Checks

def view (width : Nat) (bases : Space → Word) (initial : Space → Memory) (events : List (Event 32)) :
    Space → Nat → Word := WordView.memory initial events (bases .shared).toNat width

theorem publication_view {events : List (Event 32)} {index : Nat}
    (launch : Launch width bases start) (lo : 2≤width) (hi : width≤5)
    (run : Runs cfg (program width) start events final)
    (observed : events[index]?=some (.data reader access)) (read : access.data.store=false)
    (shared : access.space=.shared) (plane : Fin 7) (positive : plane≠0)
    (writer : Fin 32) (active : writer.val<width*width)
    (address : access.data.address=SharedPlane.address (bases .shared).toNat width plane.val writer.val)
    (later : boundary width (preceding plane)<access.data.pc)
    (compatible : Visibility.Compatible initial events source) (performed : Visibility.Performed events source) :
    access.data.value=view width bases initial events .shared access.data.address := by
  obtain ⟨w,wa,hw,value,bytes⟩ := Checks.publication width lo hi run launch.reset launch.pcs
    launch.base_nat launch.lane_nat launch.fits plane positive writer active observed later read shared address compatible performed
  have origin := compatible index reader access observed read 0
  rw [bytes 0] at origin
  obtain ⟨actualWriter,actual,actualEvent,store,space,sameAddress,_⟩ := origin
  have eq := Option.some.inj (actualEvent.symm.trans hw)
  cases eq
  have space' : wa.space=.shared := space.trans shared
  have same : wa.data.address=access.data.address := by simpa using sameAddress
  have owner := Checks.unique width lo hi run launch.reset launch.pcs launch.base_nat launch.lane_nat launch.fits hw store space'
  have outside := Geometry.plane_positive width writer.val (bases .shared).toNat plane positive
  rw [← address,← same] at outside
  rw [value,← same]
  exact (WordView.output hw store space' owner outside).symm

/-- Every load of the concrete program is justified in one word view of actual
initial bytes and stores. Address geometry and barrier ordering are both derived. -/
theorem load_view {events : List (Event 32)} {index : Nat}
    (launch : Launch width bases start) (lo : 2≤width) (hi : width≤5)
    (run : Runs cfg (program width) start events final)
    (observed : events[index]?=some (.data reader access)) (read : access.data.store=false)
    (compatible : Visibility.Compatible initial events source) (performed : Visibility.Performed events source) :
    access.data.value=view width bases initial events access.space access.data.address := by
  obtain ⟨off,address,aligned,bounds⟩ := load_location launch lo hi run (List.mem_of_getElem? observed) read
  cases space : access.space with
  | global =>
    have value := Visibility.read_only_value compatible observed read
      (by rw [space]; exact Inputs.global_readonly width lo hi run _)
    simpa [space,view,WordView.memory] using value
  | shared =>
    obtain ⟨bound,later⟩ := bounds space
    have nowrap : (bases .shared).toNat+off.toNat<2^64 := by have h := launch.fits; omega
    have natural : access.data.address=(bases .shared).toNat+off.toNat := by
      rw [address,space,BitVec.toNat_add,Nat.mod_eq_of_lt nowrap]
    obtain ⟨plane,lane,active,offset,planeIndex⟩ := Geometry.split_offset width off.toNat lo hi aligned bound
    have physical : access.data.address=SharedPlane.address (bases .shared).toNat width plane.val lane.val := by
      rw [natural,offset]; rfl
    by_cases zero : plane=0
    · subst plane
      simp only [Fin.val_zero] at physical
      have range := Geometry.plane_zero width lane.val (bases .shared).toNat active
      rw [← physical] at range
      have value := Inputs.initial_value width lo hi run launch.reset launch.pcs launch.base_nat launch.lane_nat launch.fits
        observed read (Or.inr range) compatible
      rw [space] at value
      simpa [view,WordView.memory,show access.data.address<(bases .shared).toNat+width*width*8 by omega] using value
    · exact publication_view launch lo hi run observed read space plane zero lane active physical (later plane planeIndex zero) compatible performed

theorem all_reads (launch : Launch width bases start) (lo : 2≤width) (hi : width≤5)
    (run : Runs cfg (program width) start events final)
    (compatible : Visibility.Compatible initial events source) (performed : Visibility.Performed events source) :
    Symbolic.Reads (view width bases initial events) events := by
  intro thread access member read
  obtain ⟨index,observed⟩ := List.mem_iff_getElem?.mp member
  exact load_view launch lo hi run observed read compatible performed

theorem value_invariant (launch : Launch width bases start) (lo : 2≤width) (hi : width≤5)
    (run : Runs cfg (program width) start events final)
    (compatible : Visibility.Compatible initial events source) (performed : Visibility.Performed events source) :
    Symbolic.Invariant .values (program width) (width*width) (fun t => seed width t.val) bases
      (view width bases initial events) final :=
  Symbolic.runs_invariant run launch.aligned (launch.symbolic .values _) (guards width lo hi)
    (fun _ => all_reads launch lo hi run compatible performed)

end PtxTorchLean.Poisson.PTX.Concurrent.CellMiddle.Numeric

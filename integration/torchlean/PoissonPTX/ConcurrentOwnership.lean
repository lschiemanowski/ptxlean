import PoissonPTX.ConcurrentProducer

/-! Forward-only fetched programs cannot repeat a thread's memory instruction.
Combine this control fact with physical shared-plane ownership. -/
namespace PtxTorchLean.Poisson.PTX.Concurrent
open Ptx

/-- A skipped body always lands at a later instruction. -/
def Forward (program : List Instr) : Prop :=
  ∀ pc active target : Nat, program[pc]?=some (.skip active target) → pc<target

theorem step_pc_mono {s : State n} (step : Step cfg program selected s out) (forward : Forward program)
    (thread : Fin n) : (s.lanes thread).pc≤(out.state.lanes thread).pc := by
  obtain ⟨fresh,i,fetch,h⟩ := step
  cases h with
  | data hd =>
    have pc := data_pc hd
    by_cases eq : thread=selected
    · subst thread; simp [setLane,pc]
    · simp [setLane,Function.update,eq]
  | skip =>
    have bound := forward _ _ _ fetch
    by_cases eq : thread=selected
    · subst thread
      simp only [setLane,Function.update_self]
      split <;> omega
    · simp [setLane,Function.update,eq]
  | sync => simp only [synchronize]; split <;> simp [advance]

theorem runs_pc_mono {start : State n} (run : Runs cfg program start events final) (forward : Forward program)
    (thread : Fin n) : (start.lanes thread).pc≤(final.lanes thread).pc := by
  induction run with
  | nil => rfl
  | cons step tail ih => exact (step_pc_mono step forward thread).trans ih

theorem run_access_bound (run : Runs cfg program start events final) (forward : Forward program)
    (member : Event.data thread access∈events) : (start.lanes thread).pc≤access.data.pc := by
  obtain ⟨before,earlier,selected,out,suffix,hp,hs,hm,ht,he⟩ := run_access_prefix run member
  obtain ⟨eq,op,next,fetch,hd⟩ := step_access_origin hs hm
  subst selected
  rw [access_pc hd]
  exact runs_pc_mono hp forward thread

theorem step_access_post (step : Step cfg program selected s out)
    (member : Event.data thread access∈out.events) :
    (out.state.lanes thread).pc=access.data.pc+1 := by
  obtain ⟨fresh,i,fetch,h⟩ := step
  cases h with
  | data hd =>
    cases ha : ‹Option Access› with
    | none => simp [ha] at member
    | some actual =>
      simp only [ha,Option.toList_some,List.map_cons,List.map_nil,List.mem_singleton,Event.data.injEq] at member
      obtain ⟨rfl,rfl⟩ := member
      have h := data_pc hd
      have hpc := access_pc (show Data _ _ _ (some access) by simpa [ha] using hd)
      simpa [setLane,hpc] using h
  | skip => simp at member
  | sync => simp only [synchronize] at member; split at member <;> simp_all

def AccessOrder (left right : Event n) : Prop :=
  ∀ thread a b, left=.data thread a → right=.data thread b → a.data.pc<b.data.pc

theorem step_access_order (step : Step cfg program selected s out) : out.events.Pairwise AccessOrder := by
  apply List.pairwise_iff_getElem.mpr
  intro i j hi hj hij thread a b left right
  have mem : Event.data thread a∈out.events := left ▸ List.getElem_mem hi
  have single := access_single step mem
  have length : out.events.length=1 := by rw [single]; rfl
  omega

/-- Earlier accesses of one thread have strictly smaller instruction positions,
regardless of the selected interleaving or candidate load values. -/
theorem run_access_order (run : Runs cfg program start events final) (forward : Forward program) :
    events.Pairwise AccessOrder := by
  induction run with
  | nil => simp
  | cons step tail ih =>
    apply List.pairwise_append.mpr
    refine ⟨step_access_order step,ih,?_⟩
    intro left hl right hr thread a b he hf
    subst left; subst right
    have post := step_access_post step hl
    have bound := run_access_bound tail forward hr
    omega

/-- A thread cannot emit two occurrences of one memory instruction. -/
theorem access_site_unique {events : List (Event n)} {i j : Nat}
    (run : Runs cfg program start events final) (forward : Forward program)
    (left : events[i]?=some (Event.data thread a)) (right : events[j]?=some (Event.data thread b))
    (same : a.data.pc=b.data.pc) : i=j := by
  obtain ⟨hi,he⟩ := List.getElem?_eq_some_iff.mp left
  obtain ⟨hj,hf⟩ := List.getElem?_eq_some_iff.mp right
  have ordered := run_access_order run forward
  rcases lt_trichotomy i j with lt | eq | gt
  · have h := ordered.rel_getElem_of_lt hi hj lt thread a b he hf
    omega
  · exact eq
  · have h := ordered.rel_getElem_of_lt hj hi gt thread b a hf he
    omega

/-- The structural obligation for a plane layout: every shared store comes
from an active lane, at that lane's word and at the designated plane's site.
This says nothing about stored values. It must be derived for a kernel body. -/
def PlaneStores (events : List (Event n)) (base width : Nat) (site : Fin 7 → Nat) : Prop :=
  ∀ (index : Nat) thread access, events[index]?=some (Event.data thread access) →
    access.data.store=true → access.space=.shared →
    ∃ plane : Fin 7, thread.val<width*width ∧ access.data.pc=site plane ∧
      access.data.address=SharedPlane.address base width plane.val thread.val

/-- Disjoint plane/lane bytes identify the only possible producer. Forward
control then identifies the unique event occurrence of its store. -/
theorem plane_sole_writer {events : List (Event n)} {w : Nat}
    (run : Runs cfg program start events final) (forward : Forward program)
    (coverage : PlaneStores events base width site)
    (observed : events[w]?=some (Event.data writer wa))
    (write : wa.data.store=true) (shared : wa.space=.shared) :
    Visibility.SoleWriter events w wa.data.address := by
  obtain ⟨p,hp,pcp,addrp⟩ := coverage w writer wa observed write shared
  intro other thread access ho store space j k same
  obtain ⟨q,hq,pcq,addrq⟩ := coverage other thread access ho store space
  have byteEq : SharedPlane.address base width q.val thread.val+j.val =
      SharedPlane.address base width p.val writer.val+k.val := by simpa [addrp,addrq] using same
  have planeEq : q=p := by
    by_contra ne
    have different : q.val≠p.val := fun eq => ne (Fin.ext eq)
    have disjoint := SharedPlane.planes_disjoint base width q.val p.val different ⟨thread.val,hq⟩ ⟨writer.val,hp⟩
    unfold Sources.Disjoint at disjoint
    have hj := j.isLt; have hk := k.isLt
    simp only at disjoint
    omega
  subst q
  have threadEq : thread=writer := by
    apply Fin.ext
    unfold SharedPlane.address at byteEq
    have hj := j.isLt; have hk := k.isLt
    omega
  subst thread
  exact access_site_unique run forward ho observed (pcq.trans pcp.symm)

/-- A shared read of a producer's plane entry recovers that producer's actual
store. Control supplies ordering; plane geometry and non-repetition supply
ownership. Only the necessary byte-source constraints govern read values. -/
theorem read_from_plane_producer {start : State n} {events : List (Event n)} {r : Nat}
    (run : Runs cfg program start events final)
    (reset : start.barrier=Barrier.reset generation) (forward : Forward program)
    (coverage : PlaneStores events base width site) (sites : Function.Injective site)
    (plane : Fin 7) (store : program[site plane]?=some (.data (.store64 .shared addr src)))
    (writerStops : StopsFor program writer (site plane))
    (writerInitial : (start.lanes writer).pc≤site plane) (beforeBarrier : site plane<boundary)
    (barrier : program[boundary]?=some (.sync 0)) (stops : StopsAt program boundary)
    (initial : ∀ t, (start.lanes t).pc≤boundary)
    (observed : events[r]?=some (Event.data reader ra)) (later : boundary<ra.data.pc)
    (read : ra.data.store=false) (shared : ra.space=.shared)
    (address : ra.data.address=SharedPlane.address base width plane.val writer.val)
    (compatible : Visibility.Compatible initialBytes events source)
    (performed : Visibility.Performed events source) :
    ∃ w wa, events[w]?=some (.data writer wa) ∧ wa.data.pc=site plane ∧
      Visibility.Across events w r ∧ ra.data.value=wa.data.value ∧
      ∀ k, source r k=.store w k := by
  obtain ⟨w,wa,hw,pc,write,space,ordered⟩ := producer_across run reset store writerStops
    writerInitial beforeBarrier barrier stops initial observed later
  obtain ⟨p,hp,pcp,addrp⟩ := coverage w writer wa hw write space
  have pe : p=plane := sites (pcp.symm.trans pc)
  subst p
  have same : wa.data.address=ra.data.address := addrp.trans address.symm
  have owner := plane_sole_writer run forward coverage hw write space
  rw [same] at owner
  obtain ⟨value,bytes⟩ := Visibility.read_from_writer compatible performed hw observed
    write read space shared same ordered owner
  exact ⟨w,wa,hw,pc,ordered,value,bytes⟩

end PtxTorchLean.Poisson.PTX.Concurrent

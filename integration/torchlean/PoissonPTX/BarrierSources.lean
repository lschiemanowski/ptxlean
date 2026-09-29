import PoissonPTX.ConcurrentBarrier
import PoissonPTX.SharedPlane

/-! Necessary source constraints for a closed block, generic proxy, identity
byte addresses and non-overlapping single-writer shared words. These constraints
are not complete PTX admission and do not assume any matrix result. -/
namespace PtxTorchLean.Poisson.PTX.Concurrent.Visibility
open Ptx

/-- Positions refer to actual events, with a writer's own arrival before the
common completion and a participating reader's access after it. -/
def Across (events : List (Event n)) (w r : Nat) : Prop :=
  ∃ writer reader wa ra key a c,
    events[w]?=some (.data writer wa) ∧
    events[r]?=some (.data reader ra) ∧
    events[a]?=some (.barrier (.arrival key writer)) ∧
    events[c]?=some (.barrier (.completion key)) ∧ w<a ∧ a<c ∧ c<r

/-- Every byte names initialization or a real store in the same address space. -/
def Compatible (initial : Space → Memory) (events : List (Event n))
    (source : Nat → Fin 8 → Sources.Origin Nat) : Prop :=
  ∀ r reader ra, events[r]?=some (.data reader ra) → ra.data.store=false → ∀ k,
    match source r k with
    | .initial => byte ra.data.value k.val=initial ra.space (ra.data.address+k.val)
    | .store w j => ∃ writer wa, events[w]?=some (.data writer wa) ∧
        wa.data.store=true ∧ wa.space=ra.space ∧
        wa.data.address+j.val=ra.data.address+k.val ∧
        byte ra.data.value k.val=byte wa.data.value j.val

/-- Barrier completion makes a prior shared write performed with respect to
participating readers. Consequently its covered bytes cannot still come from
initialization. Other PTX coherence/order constraints remain separate. -/
def Performed (events : List (Event n)) (source : Nat → Fin 8 → Sources.Origin Nat) : Prop :=
  ∀ w r writer reader wa ra, events[w]?=some (.data writer wa) →
    events[r]?=some (.data reader ra) → wa.data.store=true → ra.data.store=false →
    wa.space=.shared → ra.space=.shared → Across events w r →
    ∀ j k : Fin 8, wa.data.address+j.val=ra.data.address+k.val → source r k≠.initial

/-- Only the selected executed store can cover a byte of this shared word.
This is a storage-ownership condition, not an assumed value or phase answer. -/
def SoleWriter (events : List (Event n)) (w address : Nat) : Prop :=
  ∀ other thread access, events[other]?=some (.data thread access) →
    access.data.store=true → access.space=.shared → ∀ j k : Fin 8,
    access.data.address+j.val=address+k.val → other=w

/-- No whole-word atomicity assumption is needed: ownership forces every byte
source to be the same actual writer and corresponding byte offset. -/
theorem read_from_writer (compatible : Compatible initial events source)
    (performed : Performed events source)
    (hw : events[w]?=some (.data writer wa)) (hr : events[r]?=some (.data reader ra))
    (write : wa.data.store=true) (read : ra.data.store=false)
    (sw : wa.space=.shared) (sr : ra.space=.shared)
    (same : wa.data.address=ra.data.address) (ordered : Across events w r)
    (owner : SoleWriter events w ra.data.address) :
    ra.data.value=wa.data.value ∧ ∀ k, source r k=.store w k := by
  have chosen : ∀ k, source r k=.store w k ∧ byte ra.data.value k.val=byte wa.data.value k.val := by
    intro k
    have comp := compatible r reader ra hr read k
    cases hs : source r k with
    | initial => exact False.elim (performed w r writer reader wa ra hw hr write read sw sr ordered k k (by rw [same]) hs)
    | store other j =>
      simp only [hs] at comp
      obtain ⟨t,a,ha,store,space,address,value⟩ := comp
      have eq : other=w := owner other t a ha store (space.trans sr) j k address
      subst other
      have accessEq : a=wa := by have := Option.some.inj (ha.symm.trans hw); cases this; rfl
      subst a
      have jk : j=k := by apply Fin.ext; omega
      subst j
      exact ⟨rfl,value⟩
  exact ⟨Sources.word_eq_of_bytes _ _ (fun k => (chosen k).2),fun k => (chosen k).1⟩

/-- The ordering evidence includes a genuinely completed common barrier in the
fetched run, with earlier actual arrivals from every thread, including padding. -/
theorem across_arrivals {events : List (Event n)} (run : Runs cfg program start events final)
    (reset : start.barrier=Barrier.reset generation) (ordered : Across events w r) :
    ∃ key c, events[c]?=some (.barrier (.completion key)) ∧ w<c ∧ c<r ∧
      ∀ thread : Fin n, ∃ a, a<c ∧ events[a]?=some (.barrier (.arrival key thread)) := by
  obtain ⟨writer,reader,wa,ra,key,a,c,hw,hr,ha,hc,hwa,hac,hcr⟩ := ordered
  exact ⟨key,c,hc,by omega,hcr,History.completed_arrivals run reset c key hc⟩

/-- A later load equals the word in the constructed publication snapshot when
that snapshot is obtained from the very same executed store. -/
theorem read_published (compatible : Compatible initial events source)
    (performed : Performed events source)
    (hw : events[w]?=some (.data writer wa)) (hr : events[r]?=some (.data reader ra))
    (write : wa.data.store=true) (read : ra.data.store=false)
    (sw : wa.space=.shared) (sr : ra.space=.shared)
    (same : wa.data.address=ra.data.address) (ordered : Across events w r)
    (owner : SoleWriter events w ra.data.address) (snapshot : Memory)
    (published : read64 snapshot wa.data.address=wa.data.value) :
    ra.data.value=read64 snapshot ra.data.address := by
  rw [(read_from_writer compatible performed hw hr write read sw sr same ordered owner).1,
    ← same,published]

theorem ownership_of_disjoint (events : List (Event n)) (w address : Nat)
    (disjoint : ∀ other thread access, events[other]?=some (.data thread access) →
      access.data.store=true → access.space=.shared → other≠w → Sources.Disjoint access.data.address address) :
    SoleWriter events w address := by
  intro other thread access observed store space j k same
  by_contra ne
  have h := disjoint other thread access observed store space ne
  have hj := j.isLt; have hk := k.isLt
  unfold Sources.Disjoint at h
  omega

end PtxTorchLean.Poisson.PTX.Concurrent.Visibility

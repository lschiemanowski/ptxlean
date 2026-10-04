import PoissonPTX.ConcurrentReadOnly
import PoissonPTX.RepeatedShared

namespace PtxTorchLean.Poisson.PTX.Concurrent.Visibility
variable {n : Nat} {events : List (Event n)} {r : Nat} {reader : Fin n} {ra : Access}

/-- A necessary PTX 9.4 causality constraint (§§8.9.1, 8.9.5, 8.10.6) for
synchronous same-thread generic accesses at the same identity address. Actual
same-thread occurrence order gives program order; this does not order different
threads, model aliases/proxies, or assert complete PTX admission. -/
def GlobalThreadSources (events : List (Event n)) (source : Nat → Fin 8 → Sources.Origin Nat) : Prop :=
  ∀ (r w : Nat) (owner : Fin n) (ra wa : Access),
    events[r]?=some (.data owner ra) → events[w]?=some (.data owner wa) →
    ra.data.store=false → wa.data.store=true → ra.space=.global → wa.space=.global →
    ra.data.address=wa.data.address → r<w →
    ∀ j k : Fin 8, wa.data.address+j.val=ra.data.address+k.val → source r k≠.store w j

/-- If all possible writers of a read byte are later writes by that same
thread, no executed store can supply it. This derives initialization rather
than assuming the desired loaded word. -/
theorem before_own_writes_initial
    (compatible : Compatible initial events source) (admitted : GlobalThreadSources events source)
    (observed : events[r]?=some (.data reader ra)) (read : ra.data.store=false) (global : ra.space=.global)
    (writers : ∀ (w : Nat) (owner : Fin n) (wa : Access), events[w]?=some (.data owner wa) →
      wa.data.store=true → wa.space=.global → ∀ j k : Fin 8,
      wa.data.address+j.val=ra.data.address+k.val → owner=reader ∧ r<w ∧ wa.data.address=ra.data.address) :
    (∀ k, source r k=.initial) ∧ ra.data.value=read64 (initial .global) ra.data.address := by
  have chosen : ∀ k, source r k=.initial := by
    intro k
    have byteSource := compatible r reader ra observed read k
    cases picked : source r k with
    | initial => rfl
    | store w j =>
      rw [picked] at byteSource
      obtain ⟨owner,wa,found,write,space,address,value⟩ := byteSource
      have sharedSpace := space.trans global
      obtain ⟨same,later,wordAddress⟩ := writers w owner wa found write sharedSpace j k address
      subst owner
      exact False.elim (admitted r w reader ra wa observed found read write global sharedSpace wordAddress.symm later j k address picked)
  refine ⟨chosen,?_⟩
  apply Sources.word_eq_of_bytes
  intro k
  have byteSource := compatible r reader ra observed read k
  simpa only [chosen k,global,Sources.byte_read64] using byteSource

/-- Initial-byte choices satisfy the no-future constraint independently of
numerical values; a separate compatibility proof checks those actual bytes. -/
theorem initial_thread_sources : GlobalThreadSources events (fun _ _ => .initial) := by
  intro r w owner ra wa hr hw read write rg wg same before j k overlap
  simp

end PtxTorchLean.Poisson.PTX.Concurrent.Visibility

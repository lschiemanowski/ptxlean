import PoissonPTX.BarrierSources

namespace PtxTorchLean.Poisson.PTX.Concurrent.Visibility

/-- Byte sources may choose different real stores. If every covering shared
store supplies the same target byte and one such store is performed, the read
has the target word. Neither whole-word atomicity nor a unique event is needed. -/
theorem read_from_value {events : List (Event n)} {w r : Nat}
    (compatible : Compatible initial events source) (performed : Performed events source)
    (hw : events[w]?=some (.data writer wa)) (hr : events[r]?=some (.data reader ra))
    (write : wa.data.store=true) (read : ra.data.store=false)
    (sw : wa.space=.shared) (sr : ra.space=.shared)
    (same : wa.data.address=ra.data.address) (ordered : Across events w r)
    (values : ∀ (other : Nat) (thread : Fin n) (access : Access), events[other]?=some (.data thread access) →
      access.data.store=true → access.space=.shared → ∀ j k : Fin 8,
      access.data.address+j.val=ra.data.address+k.val → byte access.data.value j.val=byte value k.val) :
    ra.data.value=value := by
  apply Sources.word_eq_of_bytes
  intro k
  have comp := compatible r reader ra hr read k
  cases hs : source r k with
  | initial =>
    exact False.elim (performed w r writer reader wa ra hw hr write read sw sr ordered k k (by rw [same]) hs)
  | store other j =>
    simp only [hs] at comp
    obtain ⟨t,a,ha,store,space,address,bytes⟩ := comp
    exact bytes.trans (values other t a ha store (space.trans sr) j k address)

end PtxTorchLean.Poisson.PTX.Concurrent.Visibility

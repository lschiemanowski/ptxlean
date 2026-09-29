import PoissonPTX.ConcurrentReplay

namespace PtxTorchLean.Poisson.PTX.Concurrent.Visibility

/-- No executed store in this address space covers any of the eight read bytes. -/
def ReadOnly (events : List (Event n)) (sp : Space) (address : Nat) : Prop :=
  ∀ (w : Nat) writer wa, events[w]?=some (.data writer wa) → wa.data.store=true → wa.space=sp →
    ∀ j k : Fin 8, wa.data.address+j.val≠address+k.val

theorem read_only_initial {events : List (Event n)} {r : Nat} (compatible : Compatible initial events source)
    (observed : events[r]?=some (.data reader ra)) (read : ra.data.store=false)
    (readonly : ReadOnly events ra.space ra.data.address) :
    ∀ k, source r k=.initial := by
  intro k
  have h := compatible r reader ra observed read k
  cases hs : source r k with
  | initial => rfl
  | store w j =>
    simp only [hs] at h
    obtain ⟨writer,wa,hw,store,space,address,_⟩ := h
    exact False.elim (readonly w writer wa hw store space j k address)

theorem read_only_value {events : List (Event n)} {r : Nat} (compatible : Compatible initial events source)
    (observed : events[r]?=some (.data reader ra)) (read : ra.data.store=false)
    (readonly : ReadOnly events ra.space ra.data.address) :
    ra.data.value=read64 (initial ra.space) ra.data.address := by
  apply Sources.word_eq_of_bytes
  intro k
  have h := compatible r reader ra observed read k
  rw [read_only_initial compatible observed read readonly k] at h
  simpa using h

/-- The replay premise follows from storage ownership and byte compatibility. -/
theorem readonly_reads (compatible : Compatible initial events source)
    (readonly : ∀ a, Event.data thread a∈events → a.data.store=false →
      lo≤a.data.pc → a.data.pc<hi → ReadOnly events a.space a.data.address) :
    Replay.Reads initial thread lo hi events := by
  intro a member read before after
  obtain ⟨r,hr⟩ := List.mem_iff_getElem?.mp member
  exact read_only_value compatible hr read (readonly a member read before after)

end PtxTorchLean.Poisson.PTX.Concurrent.Visibility

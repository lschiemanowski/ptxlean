import PoissonPTX.CellGridSources

namespace PtxTorchLean.Poisson.PTX.CellGrid

abbrev IndexChoices (count : Nat) := Fin count → Nat → Fin 4 → PTX.Sources.Origin (Fin count × Nat)

/-- Integer reads refer to the same actual grid word stores as floating-point
reads. All integer loads in this fragment access the common global storage. -/
def IndexCompatible (global : Memory) (events : List (Event count)) (indices : List (Index count))
    (source : IndexChoices count) : Prop :=
  ∀ block r reader ra, (forBlock block indices)[r]?=some (reader,ra) → ∀ k,
    match source block r k with
    | .initial => IndexSources.byte32 ra.value k.val=global (ra.address+k.val)
    | .store (writerBlock,w) j => ∃ writer wa,
        (forBlock writerBlock events)[w]?=some (.data writer wa) ∧ wa.data.store=true ∧ wa.space=.global ∧
        wa.data.address+j.val=ra.address+k.val ∧ IndexSources.byte32 ra.value k.val=byte wa.data.value j.val

/-- A read below a proved global-store fence must obtain every byte from the
initial global memory. The fence is later derived from actual cell stores. -/
theorem index_initial {count : Nat} {global : Memory} {events : List (Event count)}
    {indices : List (Index count)} {source : IndexChoices count}
    {block : Fin count} {r fence : Nat} {reader : Fin 32} {ra : IndexSources.Access}
    (compatible : IndexCompatible global events indices source)
    (observed : (forBlock block indices)[r]?=some (reader,ra))
    (upper : ra.address+4≤fence)
    (lower : ∀ writerBlock writer wa, .data writer wa∈forBlock writerBlock events →
      wa.data.store=true → wa.space=.global → fence≤wa.data.address) :
    ra.value=read32 global ra.address := by
  apply IndexSources.word_eq_of_bytes
  intro k
  have h := compatible block r reader ra observed k
  cases chosen : source block r k with
  | initial => simpa [chosen,IndexSources.byte_read32] using h
  | store location j =>
    obtain ⟨writerBlock,w⟩ := location
    rw [chosen] at h
    obtain ⟨writer,wa,found,store,space,address,value⟩ := h
    have below := lower writerBlock writer wa (List.mem_of_getElem? found) store space
    have bound := k.isLt
    omega

end PtxTorchLean.Poisson.PTX.CellGrid

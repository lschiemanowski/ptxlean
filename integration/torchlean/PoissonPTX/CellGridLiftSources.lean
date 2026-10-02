import PoissonPTX.CellGridIndices

namespace PtxTorchLean.Poisson.PTX.CellGrid

/-- Lift a local source by tagging its actual writer with the same block. -/
def liftSource (block : Fin count) : PTX.Sources.Origin Nat → PTX.Sources.Origin (Fin count × Nat)
  | .initial => .initial
  | .store w j => .store (block,w) j

variable {count : Nat} {global : Memory} {memory : Fin count → Space → Memory}
  {events : List (Event count)} {indices : List (Index count)}
  {localEvents : Fin count → List (Concurrent.Event 32)}
  {localIndices : Fin count → List (Fin 32 × IndexSources.Access)}

theorem compatible_lift
    (source : Fin count → Nat → Fin 8 → PTX.Sources.Origin Nat)
    (projected : ∀ block, forBlock block events=localEvents block)
    (sameGlobal : ∀ block, memory block .global=global)
    (localCompatible : ∀ block, Concurrent.Visibility.Compatible (memory block) (localEvents block) (source block)) :
    Compatible global (fun block => memory block .shared) events
      (fun block r k => liftSource block (source block r k)) := by
  intro block r reader ra observed read k
  rw [projected] at observed
  have h := localCompatible block r reader ra observed read k
  cases chosen : source block r k with
  | initial =>
    simp only [chosen] at h
    simp only [chosen,liftSource]
    cases space : ra.space <;> simpa [initial,space,sameGlobal] using h
  | store w j =>
    simp only [chosen,liftSource]
    simp only [chosen] at h
    obtain ⟨writer,wa,found,store,space,address,value⟩ := h
    refine ⟨writer,wa,by simpa [projected] using found,store,?_,value⟩
    rw [space,address]

theorem index_compatible_lift
    (source : Fin count → Nat → Fin 4 → PTX.Sources.Origin Nat)
    (projected : ∀ block, forBlock block events=localEvents block)
    (indexProjected : ∀ block, forBlock block indices=localIndices block)
    (localCompatible : ∀ block, IndexSources.Compatible global (localEvents block) (localIndices block) (source block)) :
    IndexCompatible global events indices (fun block r k => liftSource block (source block r k)) := by
  intro block r reader ra observed k
  rw [indexProjected] at observed
  have h := localCompatible block r reader ra observed k
  cases chosen : source block r k with
  | initial => simpa only [chosen,liftSource] using h
  | store w j =>
    simp only [chosen,liftSource]
    simp only [chosen] at h
    obtain ⟨writer,wa,found,store,space,address,value⟩ := h
    exact ⟨writer,wa,by simpa [projected] using found,store,space,address,value⟩

theorem performed_lift
    (source : Fin count → Nat → Fin 8 → PTX.Sources.Origin Nat)
    (projected : ∀ block, forBlock block events=localEvents block)
    (localPerformed : ∀ block, Concurrent.Visibility.Performed (localEvents block) (source block)) :
    Performed events (fun block r k => liftSource block (source block r k)) := by
  intro block w r writer reader wa ra hw hr store read ws rs across j k address
  rw [projected] at hw hr across
  have required := localPerformed block w r writer reader wa ra hw hr store read ws rs across j k address
  cases chosen : source block r k with
  | initial => exact False.elim (required chosen)
  | store w j => simp [liftSource,chosen]

end PtxTorchLean.Poisson.PTX.CellGrid

import PoissonPTX.ObservedParallelExtend
import PoissonPTX.GlobalPublication
import PoissonPTX.GlobalThreadSources

namespace PtxTorchLean.Poisson.PTX.Flow.Parallel
open Concurrent

variable {rename : Fin n → Fin m} {words : List (Event n)} {r : Nat} {a : Access}

theorem renamed_data {owner : Fin m} (found : (words.map (renameEvent rename))[r]?=some (.data owner a)) :
    ∃ old, words[r]?=some (.data old a) ∧ rename old=owner := by
  rw [List.getElem?_map] at found
  obtain ⟨event,earlier,same⟩ := Option.map_eq_some_iff.mp found
  cases event with
  | data old access =>
    simp only [renameEvent,Event.data.injEq] at same
    obtain ⟨ownerEq,rfl⟩ := same
    exact ⟨old,earlier,ownerEq⟩
  | barrier event => cases event <;> cases same

theorem rename_data {owner : Fin n} (found : words[r]?=some (.data owner a)) :
    (words.map (renameEvent rename))[r]?=some (.data (rename owner) a) := by
  simp only [List.getElem?_map,found,Option.map_some,renameEvent]

/-- Relabeling a thread changes neither any read byte nor its source occurrence.
This supports arbitrary old source assignments, not only initialization. -/
theorem rename_compatible (compatible : Visibility.Compatible memory words sources) :
    Visibility.Compatible memory (words.map (renameEvent rename)) sources := by
  intro r reader a found read k
  obtain ⟨oldReader,oldFound,_⟩ := renamed_data found
  have old := compatible r oldReader a oldFound read k
  cases chosen : sources r k with
  | initial => simpa only [chosen] using old
  | store w j =>
    simp only [chosen] at old ⊢
    obtain ⟨writer,wa,found,store,space,address,value⟩ := old
    exact ⟨rename writer,wa,rename_data found,store,space,address,value⟩

theorem rename_index_compatible {indices : List (Fin n × IndexSources.Access)}
    (compatible : IndexSources.Compatible memory words indices sources) :
    IndexSources.Compatible memory (words.map (renameEvent rename))
      (indices.map (fun (owner,a) => (rename owner,a))) sources := by
  intro r reader a found k
  rw [List.getElem?_map] at found
  obtain ⟨⟨oldReader,oldAccess⟩,oldFound,same⟩ := Option.map_eq_some_iff.mp found
  have accessEq : oldAccess=a := (Prod.mk.inj same).2
  subst oldAccess
  have old := compatible r oldReader a oldFound k
  cases chosen : sources r k with
  | initial => simpa only [chosen] using old
  | store w j =>
    simp only [chosen] at old ⊢
    obtain ⟨writer,wa,found,store,space,address,value⟩ := old
    exact ⟨rename writer,wa,rename_data found,store,space,address,value⟩

theorem rename_thread_sources (injective : Function.Injective rename)
    (admitted : Visibility.GlobalThreadSources words sources) :
    Visibility.GlobalThreadSources (words.map (renameEvent rename)) sources := by
  intro r w owner ra wa hr hw read store rg wg same before j k address
  obtain ⟨reader,readFound,readOwner⟩ := renamed_data hr
  obtain ⟨writer,writeFound,writeOwner⟩ := renamed_data hw
  have eq : writer=reader := injective (writeOwner.trans readOwner.symm)
  subst writer
  exact admitted r w reader ra wa readFound writeFound read store rg wg same before j k address

/-- Thread renaming preserves the complete published byte memory. -/
theorem rename_publication (memory : Memory) (words : List (Event n)) :
    GlobalPublication.publish memory (words.map (renameEvent rename))=GlobalPublication.publish memory words := by
  induction words generalizing memory with
  | nil => rfl
  | cons e rest ih =>
    have one : GlobalPublication.applyEvent memory (renameEvent rename e)=GlobalPublication.applyEvent memory e := by
      cases e with
      | data => rfl
      | barrier event => cases event <;> rfl
    simpa only [List.map_cons,GlobalPublication.publish,one] using ih (GlobalPublication.applyEvent memory e)

end PtxTorchLean.Poisson.PTX.Flow.Parallel

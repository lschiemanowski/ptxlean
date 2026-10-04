import PoissonPTX.ObservedRoundedSources

namespace PtxTorchLean.Poisson.PTX.Flow.Parallel
open Concurrent
variable {rename : Fin n → Fin m} {words : List (Event n)}

theorem unrename_compatible
    (compatible : Visibility.Compatible memory (words.map (renameEvent rename)) sources) :
    Visibility.Compatible memory words sources := by
  intro r reader a found read k
  have renamed := rename_data (rename:=rename) found
  have old := compatible r (rename reader) a renamed read k
  cases chosen : sources r k with
  | initial => simpa only [chosen] using old
  | store w j =>
    simp only [chosen] at old ⊢
    obtain ⟨writer,wa,found,store,space,address,value⟩ := old
    obtain ⟨oldWriter,oldFound,_⟩ := renamed_data found
    exact ⟨oldWriter,wa,oldFound,store,space,address,value⟩

theorem unrename_index_compatible {indices : List (Fin n × IndexSources.Access)}
    (compatible : IndexSources.Compatible memory (words.map (renameEvent rename))
      (indices.map (fun (owner,a) => (rename owner,a))) sources) :
    IndexSources.Compatible memory words indices sources := by
  intro r reader a found k
  have renamed : (indices.map (fun (owner,a) => (rename owner,a)))[r]?=some (rename reader,a) := by
    simp only [List.getElem?_map,found,Option.map_some]
  have old := compatible r (rename reader) a renamed k
  cases chosen : sources r k with
  | initial => simpa only [chosen] using old
  | store w j =>
    simp only [chosen] at old ⊢
    obtain ⟨writer,wa,found,store,space,address,value⟩ := old
    obtain ⟨oldWriter,oldFound,_⟩ := renamed_data found
    exact ⟨oldWriter,wa,oldFound,store,space,address,value⟩

theorem unrename_thread_sources
    (admitted : Visibility.GlobalThreadSources (words.map (renameEvent rename)) sources) :
    Visibility.GlobalThreadSources words sources := by
  intro r w owner ra wa hr hw read store rg wg same before j k address
  exact admitted r w (rename owner) ra wa (rename_data hr) (rename_data hw) read store rg wg same before j k address

end PtxTorchLean.Poisson.PTX.Flow.Parallel

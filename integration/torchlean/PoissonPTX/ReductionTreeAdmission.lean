import PoissonPTX.ReductionTreeSources

namespace PtxTorchLean.Poisson.PTX.Concurrent.Reduction.Witness
open Visibility.Repeated

variable {left right : Word} {other r w : Nat} {access : Access} {reader writer : Fin 4}

/-- Every actual load site in the two-stage history. -/
theorem read_index (found : (history left right)[r]?=some (.data reader access))
    (read : access.data.store=false) : r=9 ∨ r=10 ∨ r=12 ∨ r=13 ∨ r=20 ∨ r=21 := by
  have bound : r<28 := (List.getElem?_eq_some_iff.mp found).1
  interval_cases r <;> simp [history,fence] at found <;> obtain ⟨rfl,rfl⟩ := found
  all_goals simp_all

/-- Every actual store, including overwritten initial and final words. -/
theorem store_index (found : (history left right)[w]?=some (.data writer access))
    (write : access.data.store=true) : w=0 ∨ w=1 ∨ w=2 ∨ w=3 ∨ w=11 ∨ w=14 ∨ w=22 := by
  have bound : w<28 := (List.getElem?_eq_some_iff.mp found).1
  interval_cases w <;> simp [history,fence] at found <;> obtain ⟨rfl,rfl⟩ := found
  all_goals simp_all

def sourceIndex (r : Nat) : Nat :=
  if r=9 then 0 else if r=10 then 2 else if r=12 then 1
  else if r=13 then 3 else if r=20 then 11 else 14

def sources (r : Nat) (k : Fin 8) : Sources.Origin Nat := .store (sourceIndex r) k

/-- The selected stores have the right address and every byte of each read. -/
theorem compatible : Visibility.Compatible (fun _ _ => 0) (history four six) sources := by
  intro r reader access found read k
  rcases read_index found read with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    simp [history,fence] at found
    obtain ⟨rfl,rfl⟩ := found
    simp [sources,sourceIndex,history,fence]

/-- Chronological coherence is one valid witness for this execution. The
necessary source contract itself still permits other coherence witnesses. -/
theorem ordered : OrderedSources (history four six) sources := by
  refine ⟨Nat.lt,?_,?_,?_⟩
  · intro a b left right la ra ha hb ls rs lsp rsp before j k address
    exact before_lt before
  · intro r w reader writer ra wa hr hw read store rs ws before j k address
    have lt := before_lt before
    intro eq
    have same : sourceIndex r=w := (Sources.Origin.store.inj eq).1
    rcases read_index hr read with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp [sourceIndex] at same; omega
  · intro w r writer reader wa ra hw hr store read ws rs before j k address
    have lt := before_lt before
    have hj := j.isLt; have hk := k.isLt
    rcases read_index hr read with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals
      rcases store_index hw store with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals
      simp [history,fence] at hw hr
      obtain ⟨rfl,rfl⟩ := hw
      obtain ⟨rfl,rfl⟩ := hr
    all_goals simp_all [sources,sourceIndex] <;> omega

/-- An actual completed fragment execution and compatible ordered sources coexist;
the universal final-value theorem is not vacuous. -/
theorem admitted_result :
    Runs cfg program start (history four six) (result four six).state ∧
    (∀ t : Fin 4, ((result four six).state.lanes t).pc=program.length) ∧
    Visibility.Compatible (fun _ _ => 0) (history four six) sources ∧
    OrderedSources (history four six) sources ∧
    (result four six).events[22]?=
      some (.data 0 ⟨.shared,⟨18,true,0,0x4024000000000000⟩⟩) :=
by
  refine ⟨actual,completed,compatible,ordered,?_⟩
  rw [executed.2]
  exact forced_final_store actual compatible ordered

/-- The overwritten initial neighbor value is impossible under the new rules,
even if a proposed execution and byte-compatible source assignment use it. -/
theorem stale_neighbor_rejected
    (run : Runs cfg program start (history four two) final)
    (compatible : Visibility.Compatible initial (history four two) source) :
    ¬OrderedSources (history four two) source := by
  intro accepted
  have forced := forced_final_inputs run compatible accepted
  exact (by decide : two≠six) forced.2.1

/-- All reads except the final neighbor use the valid witness's source; that
last read instead names the overwritten initial word of lane one. -/
def stale_sources (r : Nat) (k : Fin 8) : Sources.Origin Nat :=
  if r=21 then .store 1 k else sources r k

theorem stale_compatible :
    Visibility.Compatible (fun _ _ => 0) (history four two) stale_sources := by
  intro r reader access found read k
  rcases read_index found read with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    simp [history,fence] at found
    obtain ⟨rfl,rfl⟩ := found
    simp [stale_sources,sources,sourceIndex,history,fence]

/-- The obsolete value really can occur in candidate execution and satisfy
byte compatibility. It is specifically the ordered-source rules that reject it. -/
theorem stale_candidate : ∃ final,
    Runs cfg program start (history four two) final ∧
    Visibility.Compatible (fun _ _ => 0) (history four two) stale_sources ∧
    ¬OrderedSources (history four two) stale_sources := by
  have record : (execution four two).map Outcome.events=some (history four two) := by
    decide +kernel
  obtain ⟨out,executed,events⟩ := Option.map_eq_some_iff.mp record
  have run : Runs cfg program start (history four two) out.state :=
    events ▸ execute_sound executed
  exact ⟨out.state,run,stale_compatible,stale_neighbor_rejected run stale_compatible⟩

end PtxTorchLean.Poisson.PTX.Concurrent.Reduction.Witness

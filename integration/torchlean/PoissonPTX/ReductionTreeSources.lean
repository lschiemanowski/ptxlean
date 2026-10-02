import PoissonPTX.ReductionTreeWitness

namespace PtxTorchLean.Poisson.PTX.Concurrent.Reduction.Witness
open Visibility.Repeated

variable {left right : Word} {other r w : Nat} {access : Access} {reader writer : Fin 4}

/-- The actual guarded program is forward-only. -/
theorem forward : Forward program := by
  intro pc active target found
  have bound : pc<20 := (List.getElem?_eq_some_iff.mp found).1
  interval_cases pc <;> simp [program,SharedStore.code,PTX.Reduction.Update.code] at found
  all_goals obtain ⟨rfl,rfl⟩ := found; omega

/-- Derived from every actual store in this fetched history, including the
initial words, first replacements, and final overwrite. -/
theorem lane_stores (left right : Word) : LaneStores (history left right) 0 := by
  intro index thread access found store shared
  have bound : index<28 := (List.getElem?_eq_some_iff.mp found).1
  interval_cases index <;> simp [history,fence] at found <;> obtain ⟨rfl,rfl⟩ := found
  all_goals simp_all

theorem own_gap (found : (history left right)[other]?=some (.data 0 access))
    (store : access.data.store=true) (shared : access.space=.shared) :
    access.data.pc≤10 ∨ 15<access.data.pc := by
  have bound : other<28 := (List.getElem?_eq_some_iff.mp found).1
  interval_cases other <;> simp [history,fence] at found <;> subst access <;> simp_all

theorem neighbor_last (found : (history left right)[other]?=some (.data 1 access))
    (store : access.data.store=true) (shared : access.space=.shared) : access.data.pc≤10 := by
  have bound : other<28 := (List.getElem?_eq_some_iff.mp found).1
  interval_cases other <;> simp [history,fence] at found <;> subst access <;> simp_all

/-- The first-stage neighbor store is ordered before the final-stage load by
its actual arrival and common completion, not merely trace chronology. -/
theorem neighbor_across (left right : Word) : Visibility.Across (history left right) 14 21 :=
  ⟨1,0,⟨.shared,⟨10,true,8,six⟩⟩,⟨.shared,⟨16,false,8,right⟩⟩,
    ⟨0,0,1,11⟩,16,19,rfl,rfl,rfl,rfl,by decide,by decide,by decide⟩

/-- Arbitrary proposed final load bits are forced to the two computed first-
stage results. A future overwrite of word zero is present in this history. -/
theorem forced_final_inputs
    (run : Runs cfg program start (history left right) final)
    (compatible : Visibility.Compatible initial (history left right) source)
    (ordered : OrderedSources (history left right) source) :
    left=four ∧ right=six ∧
      (∀ k, source 20 k=.store 11 k) ∧ (∀ k, source 21 k=.store 14 k) := by
  have own := own_read run forward (lane_stores left right) compatible ordered
    (w:=11) (r:=20) (owner:=0) (wa:=⟨.shared,⟨10,true,0,four⟩⟩)
    (ra:=⟨.shared,⟨15,false,0,left⟩⟩) rfl rfl rfl rfl rfl rfl rfl (by change 10<15; decide)
    (fun _ _ found store shared => own_gap found store shared)
  have neighbor := neighbor_read run forward (lane_stores left right) compatible ordered
    (w:=14) (r:=21) (owner:=1) (reader:=0) (wa:=⟨.shared,⟨10,true,8,six⟩⟩)
    (ra:=⟨.shared,⟨16,false,8,right⟩⟩) rfl rfl rfl rfl rfl rfl rfl (neighbor_across left right)
    (fun _ _ found store shared => neighbor_last found store shared)
  exact ⟨own.1,neighbor.1,own.2,neighbor.2⟩

/-- Every admitted candidate with this executed history shape has the same
final stored result, independently of its proposed final-stage read bits. -/
theorem forced_final_store (run : Runs cfg program start (history left right) final)
    (compatible : Visibility.Compatible initial (history left right) source)
    (ordered : OrderedSources (history left right) source) :
    (history left right)[22]?=
      some (.data 0 ⟨.shared,⟨18,true,0,0x4024000000000000⟩⟩) := by
  obtain ⟨rfl,rfl,_,_⟩ := forced_final_inputs run compatible ordered
  decide +kernel

/-- Actual executed additions produce the final value ten. -/
theorem final_store :
    (result four six).events[22]?=
      some (.data 0 ⟨.shared,⟨18,true,0,0x4024000000000000⟩⟩) := by
  rw [executed.2]
  decide +kernel

end PtxTorchLean.Poisson.PTX.Concurrent.Reduction.Witness

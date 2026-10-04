import PoissonPTX.GlobalThreadSources

namespace PtxTorchLean.Poisson.PTX.Concurrent.Visibility.ThreadSourceChecks

/-- A read followed by a store of its value: compatibility alone permits an
invented nonzero word to justify itself through the later store. -/
def read : Access := ⟨.global,⟨0,false,0,1⟩⟩
def write : Access := ⟨.global,⟨1,true,0,1⟩⟩
def events : List (Event 1) := [.data 0 read,.data 0 write]
def circular : Nat → Fin 8 → Sources.Origin Nat := fun _ k => .store 1 k

theorem compatibility_alone : Compatible (fun _ _ => 0) events circular := by
  intro r owner access found isRead k
  have bound := (List.getElem?_eq_some_iff.mp found).1
  change r<2 at bound
  interval_cases r
  · simp only [events,List.getElem?_cons_zero] at found
    cases found
    exact ⟨0,write,rfl,rfl,rfl,rfl,rfl⟩
  · simp only [events,List.getElem?_cons_succ,List.getElem?_cons_zero] at found
    cases found
    cases isRead

theorem circular_rejected : ¬GlobalThreadSources events circular := by
  intro admitted
  exact admitted 0 1 0 read write rfl rfl rfl rfl rfl rfl rfl (by decide)
    0 0 rfl rfl

end PtxTorchLean.Poisson.PTX.Concurrent.Visibility.ThreadSourceChecks

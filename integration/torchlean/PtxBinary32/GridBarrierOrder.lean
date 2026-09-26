import PtxBinary32.GridHistory
import PtxBinary32.GridCompletion

/-! Each group barrier edge has real arrivals and completion positions in the
full interleaved trace, not only in a separately compressed group history. -/
namespace Ptx.Scalar.Parallel.Grid

theorem project_mem (g : Fin groups) (events : List (Event groups n)) (event : Parallel.Event n) :
    event ∈ project g events ↔ (g,event) ∈ events := by
  simp only [project,List.mem_filterMap]
  constructor
  · rintro ⟨⟨h,e⟩,inside,emitted⟩
    split at emitted
    next eq => cases eq; cases Option.some.inj emitted; exact inside
    next => contradiction
  · intro inside
    exact ⟨(g,event),inside,by simp⟩

theorem completed_arrival {s final : State groups n} {events : List (Event groups n)}
    (run : Runs cfg program s events final) (straight : Parallel.Control.Straight program)
    (reset : ∀ g, (s.blocks g).barrier=Barrier.reset generation) (g : Fin groups)
    (c : Nat) (key : Barrier.Key) (hc : events[c]?=some (g,.barrier (.completion key))) (t : Fin n) :
    ∃ a, a<c ∧ events[a]?=some (g,.barrier (.arrival key t)) := by
  have projected := (project_mem g events (.barrier (.completion key))).mpr (List.mem_of_getElem? hc)
  obtain ⟨pc,bound,atP⟩ := List.mem_iff_getElem.mp projected
  have atP' : (project g events)[pc]?=some (.barrier (.completion key)) := by simpa [bound] using atP
  obtain ⟨pa,_,atA⟩ := completed_arrivals run reset g pc key atP' t
  have actual := (project_mem g events (.barrier (.arrival key t))).mp (List.mem_of_getElem? atA)
  obtain ⟨a,ab,atA⟩ := List.mem_iff_getElem.mp actual
  have atA' : events[a]?=some (g,.barrier (.arrival key t)) := by simpa [ab] using atA
  have aligned : ∀ g, Parallel.Aligned (view s g) := by
    intro g t ht; simp [view,reset,Barrier.reset] at ht
  have order := (Control.completion_orders_sites run straight aligned c a key _ g t key.site hc atA' rfl).2
  have ne : a≠c := by intro eq; subst a; rw [hc] at atA'; simp at atA'
  exact ⟨a,by omega,atA'⟩

end Ptx.Scalar.Parallel.Grid

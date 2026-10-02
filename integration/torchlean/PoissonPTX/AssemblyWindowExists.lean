import PoissonPTX.AssemblyWindow
import PoissonPTX.ControlFlowWindowExists

namespace PtxTorchLean.Poisson.PTX.Assembly

/-- Each actual iteration consumes one remaining index; unsigned wrap is
excluded by the represented end index. No scheduling or numerical oracle is
needed for this single-thread, read-only loop fragment. -/
theorem window_exists (s : State) (frame : Stable initial s) (within : cursor s≤limit initial)
    (safe : ∀ k<limit initial, Valid (atCursor initial k) entries element) :
    ∃ t, Flow.Window.Traversal origin 19 20 (body entries element) s t := by
  have general : ∀ remaining s, limit initial-cursor s=remaining → Stable initial s →
      cursor s≤limit initial → ∃ t, Flow.Window.Traversal origin 19 20 (body entries element) s t := by
    intro remaining
    induction remaining using Nat.strong_induction_on with
    | h remaining ih =>
      intro current amount stable bound
      by_cases last : cursor current=limit initial
      · refine ⟨{current with pc:=origin+(body entries element).length+3},.done ?_⟩
        change decide (limit current≤cursor current)=true
        simp [stable_limit stable,last]
      · have inside : cursor current<limit initial := by omega
        have insideCurrent : cursor current<limit current := by rw [stable_limit stable]; exact inside
        have valid : Valid {current with pc:=origin+2} entries element := valid_at stable (safe _ inside)
        obtain ⟨middle,step⟩ := body_exists {current with pc:=origin+2} valid
        have effect := body_correct step valid
        have increment : cursor middle=cursor current+1 := cursor_increment insideCurrent effect.2.1
        have preserved : Stable initial {middle with pc:=origin} := stable_trans stable effect.2.2
        have smaller : limit initial-cursor middle<remaining := by omega
        obtain ⟨final,rest⟩ := ih (limit initial-cursor middle) smaller {middle with pc:=origin} rfl preserved
          (by change cursor middle≤limit initial; omega)
        refine ⟨final,.more ?_ step rest⟩
        simpa [Flow.Loop.exhausted,Flow.Compare.apply,cursor,limit] using insideCurrent
  exact general _ s rfl frame within

end PtxTorchLean.Poisson.PTX.Assembly

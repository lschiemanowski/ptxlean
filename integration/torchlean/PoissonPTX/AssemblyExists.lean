import PoissonPTX.AssemblyLoop
import PoissonPTX.ControlFlowLoopExists

namespace PtxTorchLean.Poisson.PTX.Assembly

/-- Each actual iteration consumes one remaining index; unsigned wrap is
excluded by the represented end index. No scheduling or numerical oracle is
needed for this single-thread, read-only loop fragment. -/
theorem traversal_exists (s : State) (frame : Stable initial s) (within : cursor s≤limit initial)
    (safe : ∀ k<limit initial, Valid (atCursor initial k) entries element) :
    ∃ t, Flow.Loop.Traversal 19 20 (body entries element) s t := by
  have general : ∀ remaining s, limit initial-cursor s=remaining → Stable initial s →
      cursor s≤limit initial → ∃ t, Flow.Loop.Traversal 19 20 (body entries element) s t := by
    intro remaining
    induction remaining using Nat.strong_induction_on with
    | h remaining ih =>
      intro current amount stable bound
      by_cases last : cursor current=limit initial
      · refine ⟨{current with pc:=(body entries element).length+4},.done ?_⟩
        change decide (limit current≤cursor current)=true
        simp [stable_limit stable,last]
      · have inside : cursor current<limit initial := by omega
        have insideCurrent : cursor current<limit current := by rw [stable_limit stable]; exact inside
        have valid : Valid {current with pc:=2} entries element := valid_at stable (safe _ inside)
        obtain ⟨middle,step⟩ := body_exists {current with pc:=2} valid
        have effect := body_correct step valid
        have increment : cursor middle=cursor current+1 := cursor_increment insideCurrent effect.2.1
        have preserved : Stable initial {middle with pc:=0} := stable_trans stable effect.2.2
        have smaller : limit initial-cursor middle<remaining := by omega
        obtain ⟨final,rest⟩ := ih (limit initial-cursor middle) smaller {middle with pc:=0} rfl preserved
          (by change cursor middle≤limit initial; omega)
        refine ⟨final,.more ?_ step rest⟩
        simpa [Flow.Loop.exhausted,Flow.Compare.apply,cursor,limit] using insideCurrent
  exact general _ s rfl frame within

theorem fetched_exists (s : Flow.State) (pc : s.core.pc=0) (running : s.halted=false)
    (within : cursor s.core≤limit s.core)
    (safe : ∀ k<limit s.core, Valid (atCursor s.core k) entries element) :
    ∃ t, Flow.Runs ctx (Flow.Loop.program 19 20 (body entries element)) s t ∧ t.halted=true ∧
      decode (t.core.regs 8)=(List.range' (cursor s.core) (limit s.core-cursor s.core)).foldl
        (fun acc k => acc+contribution s.core entries element k) (decode (s.core.regs 8)) := by
  obtain ⟨core,trace⟩ := traversal_exists s.core (stable_refl _) within safe
  obtain ⟨t,run,_,done⟩ := Flow.Loop.traversal_runs (ctx:=ctx) trace s rfl pc running
  exact ⟨t,run,done,fetched_correct run pc running done within safe⟩

end PtxTorchLean.Poisson.PTX.Assembly

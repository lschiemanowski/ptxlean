import PoissonPTX.ControlFlowWindow

namespace PtxTorchLean.Poisson.PTX.Flow.Window

/-- A structured traversal also constructs actual fetched instructions. This
reverse direction is used for existence, not as a premise of correctness. -/
theorem traversal_runs (traverse : Traversal pre.length cursor stop body core final) :
    ∀ s : State, s.core=core → s.core.pc=pre.length → s.halted=false →
      ∃ t, Runs ctx (program pre cursor stop body post) s t ∧ t.core=final ∧ t.halted=false := by
  induction traverse with
  | @done core decision =>
    intro s same pc running
    subst core
    let c := simple ctx (.compare 0 .ge (.reg cursor) (.reg stop)) s
    let b := simple ctx (.branch 0 true (pre.length+body.length+3)) c
    have cb : b.core={s.core with pc:=pre.length+body.length+3} := by
      unfold Loop.exhausted at decision
      simp [b,c,simple,next,goto,Operand.eval,decision,advance]
    refine ⟨b,?_,cb,?_⟩
    · apply Runs.cons (s:=s) (t:=c) ⟨running,.compare 0 .ge (.reg cursor) (.reg stop),by simp [program,header,pc],.simple (by intro op h; cases h)⟩
      apply Runs.cons (s:=c) (t:=b) ⟨running,.branch 0 true (pre.length+body.length+3),by simp [program,header,c,simple,next,advance,pc,List.getElem?_append_right],.simple (by intro op h; cases h)⟩
      exact .nil
    · simp [b,c,simple,next,goto,running]; split <;> rfl
  | @more core middle final decision block rest ih =>
    intro s same pc running
    subst core
    let c := simple ctx (.compare 0 .ge (.reg cursor) (.reg stop)) s
    let b := simple ctx (.branch 0 true (pre.length+body.length+3)) c
    have cb : b.core={s.core with pc:=pre.length+2} := by
      unfold Loop.exhausted at decision
      simp [b,c,simple,next,goto,Operand.eval,decision,advance,pc]
    have live : b.halted=false := by simp [b,c,simple,next,goto,running]; split <;> rfl
    have middlePC : middle.pc=pre.length+body.length+2 := by have := Indexed.block_pc block; simpa [Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using this
    let mid : State := {b with core:=middle}
    let again := simple ctx (.jump pre.length) mid
    obtain ⟨t,last,same,done⟩ := ih again rfl rfl live
    refine ⟨t,?_,same,done⟩
    apply Runs.cons (s:=s) (t:=c) ⟨running,.compare 0 .ge (.reg cursor) (.reg stop),by simp [program,header,pc],.simple (by intro op h; cases h)⟩
    apply Runs.cons (s:=c) (t:=b) ⟨running,.branch 0 true (pre.length+body.length+3),by simp [program,header,c,simple,next,advance,pc,List.getElem?_append_right],.simple (by intro op h; cases h)⟩
    have loads : Runs ctx (program pre cursor stop body post) b mid :=
      by
        have run := block_run (ctx:=ctx) (by rw [cb]; exact block) live (pre++header pre.length cursor stop body) (.jump pre.length::post) (by simp [cb,header])
        simpa [program,List.append_assoc,mid] using run
    apply append loads
    exact Runs.cons (s:=mid) (t:=again) ⟨live,.jump pre.length,by simp [mid,program,header,middlePC,List.getElem?_append_right,Nat.add_assoc],.simple (by intro op h; cases h)⟩ last

end PtxTorchLean.Poisson.PTX.Flow.Window

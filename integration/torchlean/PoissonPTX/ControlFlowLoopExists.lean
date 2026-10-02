import PoissonPTX.ControlFlowLoop

namespace PtxTorchLean.Poisson.PTX.Flow.Loop

/-- A structured traversal also constructs actual fetched instructions. This
reverse direction is used for existence, not as a premise of correctness. -/
theorem traversal_runs (traverse : Traversal cursor stop body core final) :
    ∀ s : State, s.core=core → s.core.pc=0 → s.halted=false →
      ∃ t, Runs ctx (program cursor stop body) s t ∧ t.core=final ∧ t.halted=true := by
  induction traverse with
  | @done core decision =>
    intro s same pc running
    subst core
    let c := simple ctx (.compare 0 .ge (.reg cursor) (.reg stop)) s
    let b := simple ctx (.branch 0 true (body.length+3)) c
    have cb : b.core={s.core with pc:=body.length+3} := by
      unfold exhausted at decision
      simp [b,c,simple,next,goto,Operand.eval,decision,advance]
    refine ⟨simple ctx .ret b,?_,?_,rfl⟩
    · apply Runs.cons (s:=s) (t:=c) ⟨running,.compare 0 .ge (.reg cursor) (.reg stop),by simp [program,header,pc],.simple (by intro op h; cases h)⟩
      apply Runs.cons (s:=c) (t:=b) ⟨running,.branch 0 true (body.length+3),by simp [program,header,c,simple,next,advance,pc],.simple (by intro op h; cases h)⟩
      apply Runs.cons (s:=b) (t:=simple ctx .ret b) ⟨by simp [b,c,simple,next,goto,halt,running]; split <;> rfl,
        .ret,by simp [cb,program,header],.simple (by intro op h; cases h)⟩
      exact .nil
    · simp [simple,halt,next,cb,advance]
  | @more core middle final decision block rest ih =>
    intro s same pc running
    subst core
    let c := simple ctx (.compare 0 .ge (.reg cursor) (.reg stop)) s
    let b := simple ctx (.branch 0 true (body.length+3)) c
    have cb : b.core={s.core with pc:=2} := by
      unfold exhausted at decision
      simp [b,c,simple,next,goto,Operand.eval,decision,advance,pc]
    have live : b.halted=false := by simp [b,c,simple,next,goto,running]; split <;> rfl
    have middlePC : middle.pc=body.length+2 := by have := Indexed.block_pc block; simpa [Nat.add_comm] using this
    let mid : State := {b with core:=middle}
    let again := simple ctx (.jump 0) mid
    obtain ⟨t,last,same,done⟩ := ih again rfl rfl live
    refine ⟨t,?_,same,done⟩
    apply Runs.cons (s:=s) (t:=c) ⟨running,.compare 0 .ge (.reg cursor) (.reg stop),by simp [program,header,pc],.simple (by intro op h; cases h)⟩
    apply Runs.cons (s:=c) (t:=b) ⟨running,.branch 0 true (body.length+3),by simp [program,header,c,simple,next,advance,pc],.simple (by intro op h; cases h)⟩
    have loads : Runs ctx (program cursor stop body) b mid :=
      block_run (by rw [cb]; exact block) live (header cursor stop body) [.jump 0,.ret] (by simp [cb,header])
    apply append loads
    exact Runs.cons (s:=mid) (t:=again) ⟨live,.jump 0,by simp [mid,program,header,middlePC],.simple (by intro op h; cases h)⟩ last

end PtxTorchLean.Poisson.PTX.Flow.Loop

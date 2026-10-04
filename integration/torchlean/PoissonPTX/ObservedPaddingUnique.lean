import PoissonPTX.ObservedPadding

namespace PtxTorchLean.Poisson.PTX.Flow.Observed

/-- Consume a deterministic memory-free prefix from any candidate execution.
Its register and guard results are derived from actual instruction rules. -/
theorem consume_pure (trace : Flow.Sequence ctx code s middle)
    (safe : ∀ i∈code, pure i=true) (plain : ∀ i∈code, Flow.noFP i=true)
    (forward : ∀ i∈code, Flow.linear i=true)
    (run : Runs ctx (pre++code++post) s words indices final)
    (pc : s.core.pc=pre.length) (done : final.halted=true) :
    Runs ctx (pre++code++post) middle words indices final := by
  induction trace generalizing pre with
  | nil => exact run
  | @cons i s next code middle running expected rest ih =>
    cases run with
    | nil => rw [running] at done; contradiction
    | @cons _ actual access index words indices _ step tail =>
      obtain ⟨_,op,fetch,observed⟩ := step
      have atHead : (pre++(i::code)++post)[s.core.pc]?=some i := by simp [pc]
      rw [atHead] at fetch
      cases Option.some.inj fetch
      obtain ⟨rfl,rfl⟩ := pure_observation observed (safe i (by simp))
      have replay : Flow.Eval ctx i s actual := by
        cases observed with
        | simple ordinary => exact .simple ordinary
        | data one => exact .data (Indexed.Candidate.replay one (by simp) (by simp))
      have same := Flow.eval_unique replay expected (plain i (by simp))
      subst actual
      have nextPC : next.core.pc=(pre++[i]).length := by
        rw [Flow.linear_pc expected (forward i (by simp)),pc]; simp
      simpa only [List.append_assoc,List.singleton_append,Option.toList_none,List.nil_append] using ih
        (fun i member => safe i (by simp [member])) (fun i member => plain i (by simp [member]))
        (fun i member => forward i (by simp [member]))
        (pre:=pre++[i]) (by simpa only [List.append_assoc,List.singleton_append,Option.toList_none,List.nil_append] using tail) nextPC


theorem halted_history (run : Runs ctx code s words indices final) (halted : s.halted=true) :
    final=s ∧ words=[] ∧ indices=[] := by
  cases run with
  | nil => exact ⟨rfl,rfl,rfl⟩
  | cons step _ => have running := step.1; rw [halted] at running; contradiction

/-- Every completed padding lane has precisely the pure setup result and no
memory records, independently of candidate load choices elsewhere. -/
theorem vector_padding_unique (run : Runs ctx (VectorFlowEntry.program count body) s words indices final)
    (pc : s.core.pc=0) (running : s.halted=false) (done : final.halted=true)
    (inactive : ¬Kernel.Residual.live ctx count) :
    final=Assembly.setup ctx count s ∧ words=[] ∧ indices=[] := by
  have later := consume_pure (Flow.sequence_sound (Assembly.prologue_execution (ctx:=ctx) (count:=count) running))
    (by simp [Assembly.prologue,pure]) (by simp [Assembly.prologue,Flow.noFP,Indexed.noFP])
    (by simp [Assembly.prologue,Flow.linear]) (pre:=[]) (post:=body++[.ret])
    (by simpa only [VectorFlowEntry.program,List.nil_append,List.append_assoc] using run) pc done
  exact halted_history later (Assembly.setup_inactive inactive)

end PtxTorchLean.Poisson.PTX.Flow.Observed

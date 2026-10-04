import PoissonPTX.NativeFlow

namespace PtxTorchLean.Poisson.PTX.Concurrent.NativeFlow

def targets (bound : Nat → Prop) : Flow.Instr → Prop
  | .branch _ _ target | .jump target => bound target
  | _ => True

theorem eval_upper (actual : Flow.Observed.Eval ctx i s t access index)
    (before : s.core.pc<cut) (jumps : targets (·≤cut) i) : t.core.pc≤cut := by
  cases actual with
  | data step => rw [Indexed.Candidate.data_pc step]; omega
  | simple ordinary =>
    cases i <;> simp_all [targets,Flow.simple,Flow.next,Flow.goto,Flow.halt,assign,advance]
    all_goals first | omega | (split <;> simp_all)

theorem eval_lower (actual : Flow.Observed.Eval ctx i s t access index)
    (past : cut≤s.core.pc) (jumps : targets (cut≤·) i) : cut≤t.core.pc := by
  cases actual with
  | data step => rw [Indexed.Candidate.data_pc step]; omega
  | simple ordinary =>
    cases i <;> simp_all [targets,Flow.simple,Flow.next,Flow.goto,Flow.halt,assign,advance]
    all_goals first | omega | (split <;> simp_all <;> omega)

/-- A prefix contains ordinary instructions only and cannot jump beyond its
exit. The continuation cannot jump back into it. These are syntax conditions,
independent of numerical values, source admission or execution outcomes. -/
structure Region (program : List Instr) (pre : List Flow.Instr) : Prop where
  fetch : ∀ pc, pc<pre.length → program[pc]?=pre[pc]?.map Instr.flow
  inside : ∀ pc i, pc<pre.length → pre[pc]?=some i → targets (·≤pre.length) i
  outside : ∀ pc i, pre.length≤pc → program[pc]?=some (.flow i) → targets (pre.length≤·) i

def Related (cut : Nat) (actual shadow : Flow.State) : Prop :=
  if actual.core.pc<cut then actual=shadow else shadow.core.pc=cut

theorem related_initial (s : Flow.State) (bound : s.core.pc≤cut) : Related cut s s := by
  unfold Related; split <;> simp_all; omega

theorem no_prefix_sync (region : Region program pre) (before : pc<pre.length) :
    program[pc]?≠some (.sync resource) := by
  rw [region.fetch pc before]
  cases pre[pc]? <;> simp

/-- A thread still in the input prefix cannot be advanced by another thread's
barrier completion: completion requires it at that same barrier instruction. -/
theorem sync_prefix_unchanged (region : Region program pre) {s : State n} {cfg : Config n}
    (aligned : Aligned s.core) (before : (s.core.lanes owner).pc<pre.length)
    (fetch : program[(s.core.lanes selected).pc]?=some (.sync resource)) :
    lane {s with core:=(synchronize cfg s.core selected resource).state} owner=lane s owner := by
  have blocked : (Ptx.Barrier.step (barrierConfig cfg s.core selected) s.core.barrier
      (barrierRequest cfg s.core selected resource)).disposition≠.released := by
    intro released
    have same := release_aligned cfg s.core selected resource aligned released owner
    exact no_prefix_sync region (by rw [← same]; exact before) fetch
  simp only [synchronize]
  split <;> try rfl
  exact False.elim (blocked (by assumption))

theorem sync_monotone (s : State n) (cfg : Config n) (selected owner : Fin n) (resource : Fin 16) :
    (s.core.lanes owner).pc≤((synchronize cfg s.core selected resource).state.lanes owner).pc := by
  simp only [synchronize]; split <;> simp [advance]

end PtxTorchLean.Poisson.PTX.Concurrent.NativeFlow

import PoissonPTX.ObservedParallelExtend
import PoissonPTX.ObservedPadding

namespace PtxTorchLean.Poisson.PTX.Flow.Parallel

/-- This instruction relation cannot manufacture barrier records. -/
theorem no_barriers (run : Runs ctx code start words indices final) :
    ∀ event, Concurrent.Event.barrier event∉words := by
  induction run with
  | nil => simp
  | @cons thread start next access index words indices final step rest ih =>
    intro event member
    rcases List.mem_append.mp member with first | later
    · simp at first
    · exact ih event later

theorem empty_words (run : Runs ctx code start words indices final)
    (empty : ∀ owner a, Concurrent.Event.data owner a∉words) : words=[] := by
  cases words with
  | nil => rfl
  | cons e rest =>
    cases e with
    | data owner a => exact False.elim (empty owner a (by simp))
    | barrier event => exact False.elim (no_barriers run event (by simp))

theorem silent_all (runs : ∀ t, Observed.Runs (ctx t) code (start t) [] [] (final t)) :
    Runs ctx code start [] [] final := by
  obtain ⟨words,indices,run,wordMembers,indexMembers⟩ := all_threads (fun _ => []) (fun _ => []) runs
  have wordEmpty := empty_words run (by intro owner a member; simpa using wordMembers owner a member)
  have indexEmpty : indices=[] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro pair member
    simpa using indexMembers pair.1 pair.2 member
  simpa only [wordEmpty,indexEmpty] using run

/-- Add the actual silent returns of the padding lanes after an embedded
active run. No phantom loads, stores or numerical values are added. -/
theorem complete_padding (enough : n≤m) {activeCtx : Fin n → Kernel.Context} {ctx : Fin m → Kernel.Context}
    {start final : Fin n → State} (other : Fin m → State)
    (sameContext : ∀ t, ctx (t.castLE enough)=activeCtx t)
    (run : Runs activeCtx (VectorFlowEntry.program count body) start words indices final)
    (done : ∀ t, (final t).halted=true)
    (pcs : ∀ t, n≤t.val → (other t).core.pc=0)
    (running : ∀ t, n≤t.val → (other t).halted=false)
    (inactive : ∀ t, n≤t.val → ¬Kernel.Residual.live (ctx t) count) :
    Runs ctx (VectorFlowEntry.program count body) (extend enough start other)
      (words.map (renameEvent (Fin.castLE enough)))
      (indices.map (fun (owner,a) => (owner.castLE enough,a)))
      (extend enough final (fun t => Assembly.setup (ctx t) count (other t))) ∧
    (∀ t, (extend enough final (fun t => Assembly.setup (ctx t) count (other t)) t).halted=true) := by
  have first := extend_run enough other sameContext run
  have second : Runs ctx (VectorFlowEntry.program count body) (extend enough final other) [] []
      (extend enough final (fun t => Assembly.setup (ctx t) count (other t))) := by
    apply silent_all
    intro t
    by_cases active : t.val<n
    · simp only [extend,dite_eq_left active]; exact .nil
    · simp only [extend,dite_eq_right active]
      exact (Observed.vector_padding (pcs t (by omega)) (running t (by omega)) (inactive t (by omega))).1
  refine ⟨by simpa only [List.append_nil] using append first second,?_⟩
  intro t
  by_cases active : t.val<n
  · simpa only [extend,dite_eq_left active] using done ⟨t.val,active⟩
  · simpa only [extend,dite_eq_right active] using Assembly.setup_inactive (s:=other t) (inactive t (by omega))

end PtxTorchLean.Poisson.PTX.Flow.Parallel

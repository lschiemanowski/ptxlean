import PoissonPTX.NativeFlowPrefixComplete

namespace PtxTorchLean.Poisson.PTX.Concurrent.NativeFlow

/-- Only an actual return can change a running lane into a halted lane. -/
theorem halting_eval (actual : Flow.Observed.Eval ctx i s t access index)
    (running : s.halted=false) (returned : t.halted=true) :
    t.core.pc=s.core.pc+1 ∧ ¬continues i := by
  cases actual with
  | data => simp_all
  | simple =>
    cases i <;> simp_all [continues,Flow.simple,Flow.next,Flow.goto,Flow.halt,assign,advance]
    all_goals split at returned <;> simp_all

def HaltedAfter (cut : Nat) (s : State n) : Prop :=
  ∀ owner, s.halted owner=true → cut<(s.core.lanes owner).pc

theorem step_halted_after
    (actual : Step cfg ctx program selected s out) (initial : HaltedAfter cut s)
    (noEarlyReturn : ∀ pc i, program[pc]?=some (.flow i) → pc≤cut → continues i) :
    HaltedAfter cut out.state := by
  cases actual with
  | @flow instruction _ next access index running fresh fetch effect =>
    intro owner halted
    by_cases same : owner=selected
    · subst owner
      simp only [update,Function.update_self] at halted
      have result := halting_eval effect running halted
      have after : cut<(s.core.lanes selected).pc := by
        by_contra early
        exact result.2 (noEarlyReturn _ _ fetch (by omega))
      simp only [update,setLane,Function.update_self,result.1,lane]
      omega
    · simp only [update,Function.update_of_ne same] at halted
      simpa only [update,setLane,Function.update_of_ne same] using initial owner halted
  | @sync _ resource running fresh fetch =>
    intro owner halted
    have before := initial owner halted
    have increase := sync_monotone s cfg selected owner resource
    exact Nat.lt_of_lt_of_le before increase

theorem runs_halted_after
    (actual : Runs cfg ctx program s events indices t) (initial : HaltedAfter cut s)
    (noEarlyReturn : ∀ pc i, program[pc]?=some (.flow i) → pc≤cut → continues i) :
    HaltedAfter cut t := by
  induction actual with
  | nil => exact initial
  | cons one rest ih => exact ih (step_halted_after one initial noEarlyReturn)

end PtxTorchLean.Poisson.PTX.Concurrent.NativeFlow

import PoissonPTX.HostExecution

namespace PtxTorchLean.Poisson.PTX.Host
variable {launch : Entry → Memory → Memory → Prop}

/-- Nine ordinary iteration launches, at most five fresh-residual launches and
at most three restart launches. The last-iteration restart remains included. -/
theorem loop_budget (remaining : Nat) (report : Report) :
    Budget (17*remaining) (loop a interval remaining report) := by
  induction remaining generalizing report with
  | zero => exact .finish
  | succ remaining ih =>
    unfold loop
    refine (launches_budget (entries:=iteration) (k:=8+17*remaining) ?_).weaken (by simp [iteration]; omega)
    split
    · refine (launches_budget (entries:=checkResidual) (k:=3+17*remaining) ?_).weaken (by simp [checkResidual]; omega)
      apply Budget.inspect
      intro memory
      dsimp only
      split
      · exact .finish
      · split
        · exact .finish
        · split
          · exact .finish
          · split
            · exact (launches_budget (entries:=restart) (ih _)).weaken (by simp [restart])
            · exact (ih _).weaken (by omega)
    · exact (ih _).weaken (by omega)

theorem program_budget (a : Scalar.Arena) (options : Options) :
    Budget (6+17*options.maximum) (program a options) := by
  unfold program
  refine (launches_budget (entries:=preparation) (k:=17*options.maximum) ?_).weaken (by simp [preparation])
  apply Budget.inspect
  intro memory
  dsimp only
  split
  · exact .finish
  · split
    · exact .finish
    · exact loop_budget _ _

/-- The actual host cannot issue an unbounded number of kernels: this bound
holds for every completed execution and all status values. -/
theorem program_launch_bound (actual : Execution launch (program a options) memory trace report final) :
    trace.length≤6+17*options.maximum := actual.launch_bound (program_budget a options)

theorem program_exists_of_launches (valid : Memory → Prop)
    (kernels : ∀ entry memory, valid memory → ∃ next, launch entry memory next ∧ valid next)
    (initial : valid memory) :
    ∃ trace report final, Execution launch (program a options) memory trace report final ∧ valid final :=
  (program_budget a options).execution_exists valid kernels initial

end PtxTorchLean.Poisson.PTX.Host

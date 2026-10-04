import PoissonPTX.HostCertificate

namespace PtxTorchLean.Poisson.PTX.Host
variable {n e w : Nat} {a : Layout n e w}

/-- Every host execution preserves all uploaded problem data, regardless of
status decisions, numerical exceptional values or admitted launch interleavings. -/
theorem Execution.static (actual : Execution (Launch a) plan memory trace report final) :
    a.Static memory final := by
  induction actual with
  | finish => exact a.static_refl _
  | launch step rest ih => exact Layout.static_trans step.static ih
  | inspect rest ih => exact ih

/-- The accepted solver correspondence: actual finite host/PTX execution,
unchanged uploaded equations, the exact returned solution words, zero boundary
values and the requested fresh real-valued residual bound. Acceptance is an
executable exact check, not a hypothesis asserting the desired residual bound.
Uncertified convergence, nonconvergence and external GPU fidelity are separate. -/
theorem accepted_solver
    (actual : Execution (Launch a) (program a.scalar options) initial trace report final)
    (connected : a.Connectivity initial)
    (accepted : Certificate.accept a initial final connected=true) :
    a.Static initial final ∧ trace.length≤6+17*options.maximum ∧
    ∃ values, Certificate.decode a initial final=some values ∧ Certificate.Represents a initial final values ∧
      (∀ i, (Certificate.problem a initial connected values).boundary i=true → values.solution i=0) ∧
      Poisson.Certificate.realNorm (Poisson.Certificate.residual (Certificate.problem a initial connected values) values.solution)≤
        max (values.atol : ℝ) ((values.rtol : ℝ)*Poisson.Certificate.realNorm
          (fun i => if (Certificate.problem a initial connected values).boundary i then 0 else values.rhs i)) :=
  ⟨actual.static,program_launch_bound actual,Certificate.accept_sound accepted⟩

end PtxTorchLean.Poisson.PTX.Host

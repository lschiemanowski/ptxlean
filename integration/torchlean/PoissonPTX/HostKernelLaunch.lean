import PoissonPTX.HostVectorExists
import PoissonPTX.HostScalarExists
import PoissonPTX.HostVectorFrames
import PoissonPTX.HostScalarFrames
import PoissonPTX.HostDotLaunch
import PoissonPTX.HostCellFrames
import PoissonPTX.HostInputPreservation
import PoissonPTX.HostBudget

namespace PtxTorchLean.Poisson.PTX.Host

/-- Every requested entry is executed by its concrete PTX fragment. Each
constructor carries fetched instruction execution and actual publication,
never a prescribed mathematical result. -/
inductive Launch (a : Layout n e w) : Entry → Memory → Memory → Prop where
  | vector (actual : VectorLaunch a (a.vectorCode kind) memory output) : Launch a kind.entry memory output
  | scalar (actual : ScalarLaunch a (a.scalarCode kind) memory output) : Launch a kind.entry memory output
  | dot (actual : DotLaunch a kind memory output) : Launch a kind.entry memory output
  | cell (actual : CellLaunch a kind memory output) : Launch a kind.entry memory output

variable {n e w : Nat} {a : Layout n e w}

theorem Launch.static (actual : Launch a entry memory output) : a.Static memory output := by
  cases actual with
  | vector actual => exact vector_static actual
  | scalar actual => exact scalar_static actual
  | dot actual => exact dot_static actual
  | cell actual => exact cell_static actual

/-- All host entries have finite source-admitted executions from the same
physical allocation. Only uploaded table validity is needed for indirect reads. -/
theorem launch_exists (a : Layout n e w) (entry : Entry) (memory : Memory)
    (tables : a.Coefficients) (connected : a.Connectivity memory)
    (contents : (a.assembly false).Contents memory) :
    ∃ output, Launch a entry memory output := by
  have vectors (kind : VectorEntry) : ∃ output, Launch a kind.entry memory output := by
    obtain ⟨output,run⟩ := vector_exists a kind memory contents
    exact ⟨output,.vector run⟩
  have scalars (kind : ScalarEntry) : ∃ output, Launch a kind.entry memory output := by
    obtain ⟨output,run⟩ := scalar_exists a kind memory
    exact ⟨output,.scalar run⟩
  have dots (kind : DotEntry) : ∃ output, Launch a kind.entry memory output := by
    obtain ⟨output,run⟩ := dot_exists a kind memory
    exact ⟨output,.dot run⟩
  have cells (kind : CellEntryKind) : ∃ output, Launch a kind.entry memory output := by
    obtain ⟨output,run⟩ := cell_exists a kind memory tables connected
    exact ⟨output,.cell run⟩
  cases entry
  all_goals first
    | exact cells .probe | exact cells .direction | exact cells .solution
    | exact vectors .initialize | exact vectors .updateXRZ | exact vectors .updateP
    | exact vectors .restart | exact vectors .residual | exact vectors (.assembly true) | exact vectors (.assembly false)
    | exact scalars .start | exact scalars .alpha | exact scalars .beta | exact scalars .norm | exact scalars .restart
    | exact dots .rhs | exact dots .rz | exact dots .pap | exact dots .next | exact dots .rr | exact dots .trueResidual

/-- The finite PCG driver has an actual terminating model execution, including
all requested kernel instructions and returns. This discharges the modular
host-progress obligation with the concrete PTX witnesses and static-byte frames.
It is not a claim of convergence or GPU scheduler fairness. -/
theorem solver_exists (a : Layout n e w) (options : Options) (memory : Memory)
    (tables : a.Coefficients) (connected : a.Connectivity memory)
    (contents : (a.assembly false).Contents memory) :
    ∃ trace report final,
      Execution (Launch a) (program a.scalar options) memory trace report final ∧
      a.Static memory final ∧ trace.length≤6+17*options.maximum := by
  obtain ⟨trace,report,final,actual,preserved⟩ := program_exists_of_launches
    (a:=a.scalar) (options:=options) (launch:=Launch a) (a.Static memory)
    (by
      intro entry current unchanged
      obtain ⟨next,step⟩ := launch_exists a entry current tables
        (unchanged.connectivity connected) (unchanged.assembly contents)
      exact ⟨next,step,Layout.static_trans unchanged step.static⟩)
    (a.static_refl memory)
  exact ⟨trace,report,final,actual,preserved,program_launch_bound actual⟩

end PtxTorchLean.Poisson.PTX.Host

import PtxBinary32.GridAccessControl
import PtxBinary32.GridBarrierOrder
import PtxBinary32.GridChecks
import PtxBinary32.GridCompletion
import PtxBinary32.GridControl
import PtxBinary32.GridCoverage
import PtxBinary32.GridDenseAddress
import PtxBinary32.GridDenseChecks
import PtxBinary32.GridDenseCoverage
import PtxBinary32.GridDenseDataMachine
import PtxBinary32.GridDenseDataRun
import PtxBinary32.GridDenseGlobalReads
import PtxBinary32.GridDenseOwnership
import PtxBinary32.GridDenseProgram
import PtxBinary32.GridDenseReadData
import PtxBinary32.GridDenseReadSources
import PtxBinary32.GridDenseUniversal
import PtxBinary32.GridDenseWriter
import PtxBinary32.GridExecution
import PtxBinary32.GridFlatten
import PtxBinary32.GridGraph
import PtxBinary32.GridGraphOrigins
import PtxBinary32.GridGraphUnique
import PtxBinary32.GridHistory
import PtxBinary32.GridInvariants
import PtxBinary32.GridMemory
import PtxBinary32.GridPointwise
import PtxBinary32.GridPointwiseLaunch
import PtxBinary32.GridPointwisePadding
import PtxBinary32.GridReference
import PtxBinary32.GridUnflatten
import PtxGridDenseForward
import PtxBinary32.DenseBackwardChecks
import PtxBinary32.DenseBackwardLayout
import PtxBinary32.DenseBackwardStorage
import PtxBinary32.DenseLaunchContract
import PtxBinary32.PointwiseControl
import PtxBinary32.PointwiseData
import PtxBinary32.PointwiseExists
import PtxBinary32.PointwiseLaunch
import PtxBinary32.PointwiseMachine
import PtxBinary32.PointwiseProgram
import PtxBinary32.PointwiseReads
import PtxBinary32.PointwiseUniversal
import PtxDenseBackward
import PtxBinary32.DenseData
import PtxBinary32.DenseDataFP
import PtxBinary32.DenseDataMachine
import PtxBinary32.DenseDataRules
import PtxBinary32.DenseDataRun
import PtxBinary32.DenseDataStep
import PtxBinary32.DenseGlobalReads
import PtxBinary32.DenseLaunch
import PtxBinary32.DenseLoadControl
import PtxBinary32.DenseLoadSites
import PtxBinary32.DenseReadData
import PtxBinary32.DenseReadSources
import PtxBinary32.DenseStoreData
import PtxBinary32.DenseUniversal
import PtxBinary32.ParallelLoadControl
import PtxBinary32.ParallelWriteValues
import PtxBinary32.ParallelCoverage
import PtxBinary32.DenseCoverage
import PtxBinary32.ParallelAddressControl
import PtxBinary32.ParallelStoreControl
import PtxBinary32.DenseAddressControl
import PtxBinary32.DenseOwnership
import PtxBinary32.ParallelControl
import PtxBinary32.ParallelCompletion
import PtxBinary32.ParallelVisibility
import PtxBinary32.DenseControl
import PtxBinary32.ReductionPadding
import PtxDenseForward
import PtxBinary32.ParallelChronology
import PtxBinary32.ParallelSources
import PtxBinary32.ParallelAdmission
import PtxBinary32.DenseAdmission
import PtxBinary32.ParallelConcrete
import PtxBinary32.ParallelReplay
import PtxBinary32.ParallelReplaySources
import PtxBinary32.DenseReplay
import PtxBinary32.DenseRounds
import PtxBinary32.DenseRoundPhase
import PtxBinary32.DenseOutput
import PtxBinary32.DenseForward
import PtxBinary32.DenseLayout
import PtxBinary32.DenseProgram
import PtxBinary32.DenseAddress
import PtxBinary32.ParallelSegment
import PtxBinary32.DenseSegments
import PtxBinary32.DenseArithmetic
import PtxBinary32.DenseProducts
import PtxBinary32.DenseProductPhase
import PtxBinary32.DenseChecks
import PtxBinary32.ParallelHistory
import PtxBinary32.ParallelMemory
import PtxBinary32.ParallelReference
import PtxBinary32.ParallelPublication
import PtxTensorContext
import PtxDenseVJP
import PtxBinary32.Reduction
import PtxBinary32.ReductionRelu
import PtxBinary32.Parallel
import PtxBinary32.ParallelBarrier
import PtxVectorVJP
import PtxVectorKernel
import PtxVectorAccuracy
import PtxBinary32.DotExamples
import PtxReluAccuracy
import PtxAffineBackward
import PtxAffineSquareKernel
import PtxBinary32.Affine
import PtxBinary32.Mixed
import PtxBinary32.Instructions
import PtxTorchLean
import PtxTensorBridge
import PtxBinary32
import PtxBinary32Examples
import PtxBinary32Bounds
import PtxBinary32Error

/-! Explicit public integration endpoints and binary32 reference dependencies.
Fresh elaboration is checked by check.py; imported build logs are not reused. -/

#print axioms PtxTorchLean.affineSquare
#print axioms PtxTorchLean.forward_polynomial
#print axioms PtxTorchLean.checked_vjp
#print axioms PtxTorchLean.exact_tape_success_vjp
#print axioms PtxTorchLean.checked_success
#print axioms PtxTorchLean.checked_success_vjp
#print axioms PtxTorchLean.unsigned_min_scalar_embedding

#print axioms PtxTorchLean.TensorBridge.view_apply
#print axioms PtxTorchLean.TensorBridge.view_map
#print axioms PtxTorchLean.TensorBridge.layout_bounds
#print axioms PtxTorchLean.TensorBridge.realView_eq_map
#print axioms PtxTorchLean.TensorBridge.completed_unsigned
#print axioms PtxTorchLean.TensorBridge.completed_unsigned_tensor
#print axioms PtxTorchLean.TensorBridge.completed_real_add
#print axioms PtxTorchLean.TensorBridge.completed_bounds
#print axioms PtxTorchLean.TensorBridge.candidate_unsigned_tensor
#print axioms PtxTorchLean.TensorBridge.candidate_execution_agree
#print axioms PtxTorchLean.TensorBridge.execution_exists
#print axioms PtxTorchLean.TensorBridge.real_execution_exists
#print axioms PtxTorchLean.TensorBridge.view_bounded_apply
#print axioms PtxTorchLean.TensorBridge.wraparound_execution
#print axioms PtxTorchLean.TensorBridge.wraparound_not_fitting

#print axioms Ptx.Binary32.encode_decode
#print axioms Ptx.Binary32.decode_encode
#print axioms Ptx.Binary32.finiteReal_none
#print axioms Ptx.Binary32.finiteReal_some
#print axioms Ptx.Binary32.finiteReal_isSome
#print axioms Ptx.Binary32.finite_not_nan
#print axioms Ptx.Binary32.envelope_self
#print axioms Ptx.Binary32.envelope_exists
#print axioms Ptx.Binary32.envelope_nan
#print axioms Ptx.Binary32.envelope_non_nan
#print axioms Ptx.Binary32.envelope_finite_eq
#print axioms Ptx.Binary32.envelope_finite
#print axioms Ptx.Binary32.results_exists
#print axioms Ptx.Binary32.reference_round
#print axioms Ptx.Binary32.results_round
#print axioms Ptx.Binary32.results_abs_error
#print axioms Ptx.Binary32.decode
#print axioms Ptx.Binary32.encode
#print axioms Ptx.Binary32.isNaN
#print axioms Ptx.Binary32.isFinite
#print axioms Ptx.Binary32.finiteReal
#print axioms Ptx.Binary32.Envelope
#print axioms Ptx.Binary32.reference
#print axioms Ptx.Binary32.Results
#print axioms Ptx.Binary32.exact

#print axioms Ptx.Binary32.Examples.signed_zero_bits_distinct
#print axioms Ptx.Binary32.Examples.zero_signs_finite
#print axioms Ptx.Binary32.Examples.smallest_subnormal
#print axioms Ptx.Binary32.Examples.normal_boundary
#print axioms Ptx.Binary32.Examples.ordinary_add
#print axioms Ptx.Binary32.Examples.tie_even_down
#print axioms Ptx.Binary32.Examples.tie_odd_up
#print axioms Ptx.Binary32.Examples.subnormal_add_preserved
#print axioms Ptx.Binary32.Examples.negative_zero_product
#print axioms Ptx.Binary32.Examples.zero_sign_add
#print axioms Ptx.Binary32.Examples.finite_inputs_overflow
#print axioms Ptx.Binary32.Examples.infinity_opposite_invalid
#print axioms Ptx.Binary32.Examples.infinity_times_zero_invalid
#print axioms Ptx.Binary32.Examples.nan_payload_freedom
#print axioms Ptx.Binary32.Examples.signaling_nan_envelope
#print axioms Ptx.Binary32.Examples.exceptional_not_real

#print axioms Ptx.Binary32.Bounds.maxFinite_eq
#print axioms Ptx.Binary32.Bounds.finiteReal_spec
#print axioms Ptx.Binary32.Bounds.reference_finite
#print axioms Ptx.Binary32.Bounds.round_of_range
#print axioms Ptx.Binary32.Bounds.results_error
#print axioms Ptx.Binary32.Bounds.finite_result_exists
#print axioms Ptx.Binary32.Bounds.add_range_of_magnitudes
#print axioms Ptx.Binary32.Bounds.mul_range_of_magnitudes
#print axioms Ptx.Binary32.Bounds.unit_range
#print axioms Ptx.Binary32.Bounds.positive_one_real
#print axioms Ptx.Binary32.Bounds.negative_one_real
#print axioms Ptx.Binary32.Bounds.one_negative_one_results

#print axioms Ptx.Binary32.Error.budget_nonnegative
#print axioms Ptx.Binary32.Error.add_propagation
#print axioms Ptx.Binary32.Error.mul_propagation
#print axioms Ptx.Binary32.Error.add_results
#print axioms Ptx.Binary32.Error.mul_results
#print axioms Ptx.Binary32.Error.add_exists
#print axioms Ptx.Binary32.Error.mul_exists
#print axioms Ptx.Binary32.Error.rounded_add_range
#print axioms Ptx.Binary32.Error.affine_results
#print axioms Ptx.Binary32.Error.affine_exists

#print axioms Ptx.Scalar.Binary32.Instr
#print axioms Ptx.Scalar.Binary32.Occurrence
#print axioms Ptx.Scalar.Binary32.occurrence
#print axioms Ptx.Scalar.Binary32.SupportedTarget
#print axioms Ptx.Scalar.Binary32.Eval
#print axioms Ptx.Scalar.Binary32.Step
#print axioms Ptx.Scalar.Binary32.eval_true_iff
#print axioms Ptx.Scalar.Binary32.eval_false_iff
#print axioms Ptx.Scalar.Binary32.eval_destination
#print axioms Ptx.Scalar.Binary32.eval_frame
#print axioms Ptx.Scalar.Binary32.eval_other
#print axioms Ptx.Scalar.Binary32.eval_event
#print axioms Ptx.Scalar.Binary32.eval_exists
#print axioms Ptx.Scalar.Binary32.step_origin
#print axioms Ptx.Scalar.Binary32.step_exists
#print axioms Ptx.Scalar.Binary32.step_no_fetch
#print axioms Ptx.Scalar.Binary32.step_unsupported_target
#print axioms Ptx.Scalar.Binary32.Text.mnemonic
#print axioms Ptx.Scalar.Binary32.Text.supportedMnemonic
#print axioms Ptx.Scalar.Binary32.Text.decode
#print axioms Ptx.Scalar.Binary32.Text.encode
#print axioms Ptx.Scalar.Binary32.Text.decode_encode
#print axioms Ptx.Scalar.Binary32.Text.decode_iff
#print axioms Ptx.Scalar.Binary32.signed_zero_bits
#print axioms Ptx.Scalar.Binary32.subnormal_bits
#print axioms Ptx.Scalar.Binary32.negative_guard_exec
#print axioms Ptx.Scalar.Binary32.negative_guard_skip
#print axioms Ptx.Scalar.Binary32.alias_add_bits

#print axioms Ptx.Scalar.Mixed.Instr
#print axioms Ptx.Scalar.Mixed.Event
#print axioms Ptx.Scalar.Mixed.Event.memory
#print axioms Ptx.Scalar.Mixed.Event.pc
#print axioms Ptx.Scalar.Mixed.Event.instruction
#print axioms Ptx.Scalar.Mixed.Outcome
#print axioms Ptx.Scalar.Mixed.liftScalar
#print axioms Ptx.Scalar.Mixed.Eval
#print axioms Ptx.Scalar.Mixed.Eligible
#print axioms Ptx.Scalar.Mixed.Dispatch
#print axioms Ptx.Scalar.Mixed.eligible_binary32
#print axioms Ptx.Scalar.Mixed.eval_scalar_iff
#print axioms Ptx.Scalar.Mixed.eval_binary32_iff
#print axioms Ptx.Scalar.Mixed.dispatch_fetch
#print axioms Ptx.Scalar.Mixed.dispatch_missing
#print axioms Ptx.Scalar.Mixed.dispatch_exists
#print axioms Ptx.Scalar.Mixed.Path
#print axioms Ptx.Scalar.Mixed.Advances
#print axioms Ptx.Scalar.Mixed.Path.append
#print axioms Ptx.Scalar.Mixed.Path.invariant
#print axioms Ptx.Scalar.Mixed.Path.event_origin
#print axioms Ptx.Scalar.Mixed.Run
#print axioms Ptx.Scalar.Mixed.Run.not_exhausted
#print axioms Ptx.Scalar.Mixed.scalar_next_iff
#print axioms Ptx.Scalar.Mixed.scalar_halted_iff
#print axioms Ptx.Scalar.Mixed.eval_event_origin
#print axioms Ptx.Scalar.Mixed.dispatch_event_origin
#print axioms Ptx.Scalar.Mixed.eval_next_safe
#print axioms Ptx.Scalar.Mixed.eval_halted
#print axioms Ptx.Scalar.Mixed.dispatch_next_safe
#print axioms Ptx.Scalar.Mixed.dispatch_halted
#print axioms Ptx.Scalar.Mixed.Path.memory_length
#print axioms Ptx.Scalar.Mixed.Path.memory_safe
#print axioms Ptx.Scalar.Mixed.Run.memory_length
#print axioms Ptx.Scalar.Mixed.Run.memory_safe
#print axioms Ptx.Scalar.Mixed.StoresTo
#print axioms Ptx.Scalar.Mixed.eval_frame
#print axioms Ptx.Scalar.Mixed.dispatch_frame
#print axioms Ptx.Scalar.Mixed.Path.frame
#print axioms Ptx.Scalar.Mixed.Run.frame
#print axioms Ptx.Scalar.Mixed.Run.unfold
#print axioms Ptx.Scalar.Mixed.Run.scalar_next_iff
#print axioms Ptx.Scalar.Mixed.Run.scalar_halted_iff
#print axioms Ptx.Scalar.Mixed.Run.binary32_iff

#print axioms Ptx.Scalar.Affine.load
#print axioms Ptx.Scalar.Affine.multiply
#print axioms Ptx.Scalar.Affine.addition
#print axioms Ptx.Scalar.Affine.store
#print axioms Ptx.Scalar.Affine.exit
#print axioms Ptx.Scalar.Affine.program
#print axioms Ptx.Scalar.Affine.Initial
#print axioms Ptx.Scalar.Affine.input
#print axioms Ptx.Scalar.Affine.outputIndex
#print axioms Ptx.Scalar.Affine.afterLeft
#print axioms Ptx.Scalar.Affine.afterRight
#print axioms Ptx.Scalar.Affine.afterBias
#print axioms Ptx.Scalar.Affine.afterMultiply
#print axioms Ptx.Scalar.Affine.afterAdd
#print axioms Ptx.Scalar.Affine.finish
#print axioms Ptx.Scalar.Affine.loadEvent
#print axioms Ptx.Scalar.Affine.trace
#print axioms Ptx.Scalar.Affine.run_iff
#print axioms Ptx.Scalar.Affine.run_exists
#print axioms Ptx.Scalar.Affine.trace_length
#print axioms Ptx.Scalar.Affine.trace_positions
#print axioms Ptx.Scalar.Affine.trace_instructions
#print axioms Ptx.Scalar.Affine.trace_memory
#print axioms Ptx.Scalar.Affine.finish_frame
#print axioms Ptx.Scalar.Affine.finish_registers
#print axioms Ptx.Scalar.Affine.finish_other_register
#print axioms Ptx.Scalar.Affine.finish_output
#print axioms Ptx.Scalar.Affine.finish_other_memory
#print axioms Ptx.Scalar.Affine.run_completed
#print axioms Ptx.Scalar.Affine.stored_error
#print axioms Ptx.Scalar.Affine.advance_pc
#print axioms Ptx.Scalar.Affine.path_control
#print axioms Ptx.Scalar.Affine.path_bound
#print axioms Ptx.Scalar.Affine.memoryProjection
#print axioms Ptx.Scalar.Affine.memoryWitness
#print axioms Ptx.Scalar.Affine.memoryWitness_valid
#print axioms Ptx.Scalar.Affine.trace_memory_witness
#print axioms Ptx.Scalar.Affine.run_memory_witness
#print axioms Ptx.Scalar.Affine.eventAt
#print axioms Ptx.Scalar.Affine.RegisterDependency
#print axioms Ptx.Scalar.Affine.register_dependency_forward
#print axioms Ptx.Scalar.Affine.register_dependency_acyclic
#print axioms Ptx.Scalar.Affine.run_grounded
#print axioms Ptx.Scalar.Affine.disjointFixture
#print axioms Ptx.Scalar.Affine.disjoint_example
#print axioms Ptx.Scalar.Affine.aliasFixture
#print axioms Ptx.Scalar.Affine.all_alias_example

-- Serialized storage, actual two-kernel forward and generated exact backward.
#print axioms Ptx.Scalar.Sequential.Argument
#print axioms Ptx.Scalar.Sequential.Seed
#print axioms Ptx.Scalar.Sequential.start
#print axioms Ptx.Scalar.Sequential.start_pc
#print axioms Ptx.Scalar.Sequential.start_regs
#print axioms Ptx.Scalar.Sequential.start_preds
#print axioms Ptx.Scalar.Sequential.start_memory
#print axioms Ptx.Scalar.Sequential.start_argument
#print axioms Ptx.Scalar.Sequential.start_other
#print axioms Ptx.Scalar.Sequential.Request
#print axioms Ptx.Scalar.Sequential.SuccessfulLaunch
#print axioms Ptx.Scalar.Sequential.SuccessfulLaunch.cell
#print axioms Ptx.Scalar.Sequential.SuccessfulLaunch.present
#print axioms Ptx.Scalar.Sequential.SuccessfulLaunch.owner
#print axioms Ptx.Scalar.Sequential.SuccessfulLaunch.identities
#print axioms Ptx.Scalar.Sequential.SuccessfulLaunch.run
#print axioms Ptx.Scalar.Sequential.SuccessfulLaunch.writeback
#print axioms Ptx.Scalar.Sequential.launch_exists
#print axioms Ptx.Scalar.Sequential.SuccessfulLaunch.exact_writeback
#print axioms Ptx.Scalar.Sequential.SuccessfulLaunch.run_from
#print axioms Ptx.Scalar.Sequential.SuccessfulLaunch.writeback_lookup
#print axioms Ptx.Scalar.Sequential.SuccessfulLaunch.environment_unchanged
#print axioms Ptx.Scalar.Sequential.SuccessfulLaunch.other_cell
#print axioms Ptx.Scalar.Sequential.SuccessfulLaunch.environment_safe
#print axioms Ptx.Scalar.Sequential.SuccessfulLaunch.final_environment_safe
#print axioms Ptx.Scalar.Sequential.SuccessfulLaunch.word_frame
#print axioms Ptx.Scalar.Sequential.SuccessfulLaunch.storage_step
#print axioms Ptx.Scalar.Sequential.no_launch_absent
#print axioms Ptx.Scalar.Sequential.no_launch_wrong_owner
#print axioms Ptx.Scalar.Sequential.no_launch_wrong_identity
#print axioms Ptx.Scalar.Sequential.no_launch_after_release
#print axioms Ptx.Scalar.Sequential.Chain
#print axioms Ptx.Scalar.Sequential.Chain.append
#print axioms Ptx.Scalar.Sequential.Chain.cons_iff
#print axioms Ptx.Scalar.Sequential.Chain.nil_iff
#print axioms Ptx.Scalar.Sequential.Chain.two_iff
#print axioms Ptx.Scalar.Sequential.Chain.storage_history
#print axioms Ptx.Scalar.Sequential.Chain.invariant
#print axioms Ptx.Scalar.Sequential.Chain.old_absent
#print axioms PtxTorchLean.AffineSquareVJP.scalarShape
#print axioms PtxTorchLean.AffineSquareVJP.inputs
#print axioms PtxTorchLean.AffineSquareVJP.graph
#print axioms PtxTorchLean.AffineSquareVJP.sensitivities
#print axioms PtxTorchLean.AffineSquareVJP.forward_value
#print axioms PtxTorchLean.AffineSquareVJP.generated_vjp
#print axioms PtxTorchLean.AffineSquareVJP.forward_tensor
#print axioms PtxTorchLean.AffineSquareVJP.checked_result
#print axioms PtxTorchLean.AffineSquareVJP.sensitivities_adjoint
#print axioms PtxTorchLean.AffineSquareVJP.checked_example
#print axioms Ptx.Binary32.SquareError.roundedAffine
#print axioms Ptx.Binary32.SquareError.Results
#print axioms Ptx.Binary32.SquareError.budget
#print axioms Ptx.Binary32.SquareError.zero_real
#print axioms Ptx.Binary32.SquareError.affine_value
#print axioms Ptx.Binary32.SquareError.budget_expansion
#print axioms Ptx.Binary32.SquareError.results_error
#print axioms Ptx.Binary32.SquareError.results_exists
#print axioms PtxTorchLean.AffineSquareKernel.memory
#print axioms PtxTorchLean.AffineSquareKernel.outputMemory
#print axioms PtxTorchLean.AffineSquareKernel.firstArgs
#print axioms PtxTorchLean.AffineSquareKernel.secondArgs
#print axioms PtxTorchLean.AffineSquareKernel.firstStart
#print axioms PtxTorchLean.AffineSquareKernel.secondStart
#print axioms PtxTorchLean.AffineSquareKernel.request
#print axioms PtxTorchLean.AffineSquareKernel.firstRequest
#print axioms PtxTorchLean.AffineSquareKernel.secondRequest
#print axioms PtxTorchLean.AffineSquareKernel.first_initial
#print axioms PtxTorchLean.AffineSquareKernel.second_initial
#print axioms PtxTorchLean.AffineSquareKernel.first_run_iff
#print axioms PtxTorchLean.AffineSquareKernel.second_run_iff
#print axioms PtxTorchLean.AffineSquareKernel.first_memory
#print axioms PtxTorchLean.AffineSquareKernel.second_memory
#print axioms PtxTorchLean.AffineSquareKernel.launches_correct
#print axioms PtxTorchLean.AffineSquareKernel.pipeline_of_results
#print axioms PtxTorchLean.AffineSquareKernel.pipeline_exists
#print axioms PtxTorchLean.AffineSquareKernel.pipeline_correct
#print axioms PtxTorchLean.AffineSquareKernel.pipeline_frame
#print axioms PtxTorchLean.AffineSquareKernel.stored_forward_error
#print axioms PtxTorchLean.AffineSquareKernel.two_launch_example
#print axioms PtxTorchLean.AffineSquareKernel.second_launch_after_release_rejected

-- Independently authored recomputing backward: executions, values and generated VJP.
#print axioms Ptx.Binary32.BackwardError.roundedProduct
#print axioms Ptx.Binary32.BackwardError.roundedBase
#print axioms Ptx.Binary32.BackwardError.StageRange
#print axioms Ptx.Binary32.BackwardError.Guards
#print axioms Ptx.Binary32.BackwardError.stageBudget
#print axioms Ptx.Binary32.BackwardError.qBudget
#print axioms Ptx.Binary32.BackwardError.baseBudget
#print axioms Ptx.Binary32.BackwardError.parameterBudget
#print axioms Ptx.Binary32.BackwardError.Results
#print axioms Ptx.Binary32.BackwardError.two_real
#print axioms Ptx.Binary32.BackwardError.stage_error
#print axioms Ptx.Binary32.BackwardError.results_error
#print axioms Ptx.Binary32.BackwardError.results_exists
#print axioms Ptx.GradientView.Triple
#print axioms Ptx.GradientView.Words
#print axioms Ptx.GradientView.decode
#print axioms Ptx.GradientView.component
#print axioms Ptx.GradientView.Componentwise
#print axioms Ptx.GradientView.Approximates
#print axioms Ptx.GradientView.component_inputs
#print axioms Ptx.GradientView.componentwise_iff
#print axioms Ptx.GradientView.componentwise_inputs_iff
#print axioms Ptx.GradientView.decode_of_finite
#print axioms Ptx.GradientView.decode_some_iff
#print axioms Ptx.GradientView.decode_none_iff
#print axioms Ptx.GradientView.nonfinite_rejected
#print axioms Ptx.GradientView.not_approximates_of_nonfinite
#print axioms Ptx.GradientView.approximates_iff
#print axioms Ptx.GradientView.generated_iff
#print axioms Ptx.GradientView.generated_of_bounds_checked
#print axioms Ptx.GradientView.signed_zero_same_view
#print axioms Ptx.Scalar.BackwardPipeline.Data
#print axioms Ptx.Scalar.BackwardPipeline.Data.words
#print axioms Ptx.Scalar.BackwardPipeline.Data.left
#print axioms Ptx.Scalar.BackwardPipeline.Data.right
#print axioms Ptx.Scalar.BackwardPipeline.Data.update
#print axioms Ptx.Scalar.BackwardPipeline.outputData
#print axioms Ptx.Scalar.BackwardPipeline.arguments
#print axioms Ptx.Scalar.BackwardPipeline.stageStart
#print axioms Ptx.Scalar.BackwardPipeline.request
#print axioms Ptx.Scalar.BackwardPipeline.requests
#print axioms Ptx.Scalar.BackwardPipeline.Results
#print axioms Ptx.Scalar.BackwardPipeline.stage_initial
#print axioms Ptx.Scalar.BackwardPipeline.stage_run_iff
#print axioms Ptx.Scalar.BackwardPipeline.finish_words
#print axioms Ptx.Scalar.BackwardPipeline.stage_launch_correct
#print axioms Ptx.Scalar.BackwardPipeline.stage_of_results
#print axioms Ptx.Scalar.BackwardPipeline.stage_trace_safe
#print axioms Ptx.Scalar.BackwardPipeline.results_exists
#print axioms Ptx.Scalar.BackwardPipeline.four_launches_iff
#print axioms Ptx.Scalar.BackwardPipeline.launches_correct
#print axioms Ptx.Scalar.BackwardPipeline.pipeline_correct
#print axioms Ptx.Scalar.BackwardPipeline.pipeline_of_results
#print axioms Ptx.Scalar.BackwardPipeline.pipeline_exists
#print axioms Ptx.Scalar.BackwardPipeline.pipeline_other_allocation
#print axioms Ptx.Scalar.BackwardPipeline.words_tail
#print axioms Ptx.Scalar.BackwardPipeline.pipeline_memory_frame
#print axioms Ptx.Scalar.BackwardPipeline.stage_after_release_rejected
#print axioms PtxTorchLean.AffineBackward.Data
#print axioms PtxTorchLean.AffineBackward.recomputeArgs
#print axioms PtxTorchLean.AffineBackward.withSaved
#print axioms PtxTorchLean.AffineBackward.recomputeStart
#print axioms PtxTorchLean.AffineBackward.recomputeRequest
#print axioms PtxTorchLean.AffineBackward.requests
#print axioms PtxTorchLean.AffineBackward.recompute_initial
#print axioms PtxTorchLean.AffineBackward.recompute_run_iff
#print axioms PtxTorchLean.AffineBackward.recompute_memory
#print axioms PtxTorchLean.AffineBackward.recompute_correct
#print axioms PtxTorchLean.AffineBackward.recompute_exists
#print axioms PtxTorchLean.AffineBackward.budgetX
#print axioms PtxTorchLean.AffineBackward.budgetW
#print axioms PtxTorchLean.AffineBackward.budgetB
#print axioms PtxTorchLean.AffineBackward.results_approximate
#print axioms PtxTorchLean.AffineBackward.pipeline_correct
#print axioms PtxTorchLean.AffineBackward.pipeline_exists
#print axioms PtxTorchLean.AffineBackward.pipeline_other_allocation
#print axioms PtxTorchLean.AffineBackward.stored_backward_approximation
#print axioms PtxTorchLean.AffineBackward.fixture
#print axioms PtxTorchLean.AffineBackward.five_launch_example

-- ReLU neuron: actual generated backward, finite gate, execution and accuracy.
#print axioms PtxTorchLean.ReluVJP.scalarShape
#print axioms Ptx.Binary32.Relu.positive
#print axioms Ptx.Binary32.Relu.gate
#print axioms Ptx.Binary32.Relu.forward
#print axioms Ptx.Binary32.Relu.positive_iff
#print axioms Ptx.Binary32.Relu.zero_real
#print axioms Ptx.Binary32.Relu.gate_real
#print axioms Ptx.Binary32.Relu.forward_real
#print axioms Ptx.Binary32.Relu.forward_error
#print axioms Ptx.Binary32.Relu.sign_stable
#print axioms Ptx.Scalar.ReluGate.load
#print axioms Ptx.Scalar.ReluGate.zeroTest
#print axioms Ptx.Scalar.ReluGate.signTest
#print axioms Ptx.Scalar.ReluGate.clear
#print axioms Ptx.Scalar.ReluGate.store
#print axioms Ptx.Scalar.ReluGate.exit
#print axioms Ptx.Scalar.ReluGate.program
#print axioms Ptx.Scalar.ReluGate.Initial
#print axioms Ptx.Scalar.ReluGate.input
#print axioms Ptx.Scalar.ReluGate.afterLeft
#print axioms Ptx.Scalar.ReluGate.afterRight
#print axioms Ptx.Scalar.ReluGate.afterZeroTest
#print axioms Ptx.Scalar.ReluGate.afterZero
#print axioms Ptx.Scalar.ReluGate.afterSignTest
#print axioms Ptx.Scalar.ReluGate.afterClear
#print axioms Ptx.Scalar.ReluGate.finish
#print axioms Ptx.Scalar.ReluGate.run_iff
#print axioms Ptx.Scalar.ReluGate.run_exists
#print axioms Ptx.Scalar.ReluGate.run_memory
#print axioms PtxTorchLean.ReluVJP.inputs
#print axioms PtxTorchLean.ReluVJP.rawGraph
#print axioms PtxTorchLean.ReluVJP.graph
#print axioms PtxTorchLean.ReluVJP.gate
#print axioms PtxTorchLean.ReluVJP.sensitivities
#print axioms PtxTorchLean.ReluVJP.generated_vjp
#print axioms PtxTorchLean.ReluVJP.forward_value
#print axioms PtxTorchLean.ReluVJP.checked_result
#print axioms PtxTorchLean.ReluVJP.graph_correct_at
#print axioms PtxTorchLean.ReluVJP.sensitivities_adjoint
#print axioms PtxTorchLean.ReluKernel.Data
#print axioms PtxTorchLean.ReluKernel.Data.words
#print axioms PtxTorchLean.ReluKernel.Stage
#print axioms PtxTorchLean.ReluKernel.Stage.isGate
#print axioms PtxTorchLean.ReluKernel.program
#print axioms PtxTorchLean.ReluKernel.arguments
#print axioms PtxTorchLean.ReluKernel.Data.update
#print axioms PtxTorchLean.ReluKernel.Results
#print axioms PtxTorchLean.ReluKernel.stageStart
#print axioms PtxTorchLean.ReluKernel.request
#print axioms PtxTorchLean.ReluKernel.forwardStages
#print axioms PtxTorchLean.ReluKernel.backwardStages
#print axioms PtxTorchLean.ReluKernel.Evaluation
#print axioms PtxTorchLean.ReluKernel.run_correct
#print axioms PtxTorchLean.ReluKernel.run_exists
#print axioms PtxTorchLean.ReluKernel.launch_correct
#print axioms PtxTorchLean.ReluKernel.launch_exists
#print axioms PtxTorchLean.ReluKernel.pipeline_correct
#print axioms PtxTorchLean.ReluKernel.pipeline_exists
#print axioms PtxTorchLean.ReluKernel.launch_memory_safe
#print axioms PtxTorchLean.ReluKernel.pipeline_frame
#print axioms PtxTorchLean.ReluKernel.Evaluation.inputs_frame
#print axioms PtxTorchLean.ReluKernel.forward_values
#print axioms PtxTorchLean.ReluKernel.backward_values
#print axioms PtxTorchLean.ReluKernel.Inputs
#print axioms PtxTorchLean.ReluKernel.Inputs.budget
#print axioms PtxTorchLean.ReluKernel.Inputs.affine
#print axioms PtxTorchLean.ReluKernel.forward_accuracy
#print axioms PtxTorchLean.ReluKernel.BackwardInputs
#print axioms PtxTorchLean.ReluKernel.BackwardInputs.actualGate
#print axioms PtxTorchLean.ReluKernel.BackwardInputs.idealGate
#print axioms PtxTorchLean.ReluKernel.BackwardInputs.dxBudget
#print axioms PtxTorchLean.ReluKernel.BackwardInputs.dwBudget
#print axioms PtxTorchLean.ReluKernel.BackwardInputs.away
#print axioms PtxTorchLean.ReluKernel.backward_accuracy
#print axioms PtxTorchLean.ReluKernel.stored_forward_accuracy
#print axioms PtxTorchLean.ReluKernel.stored_backward_accuracy

-- Sequential dot product and all-choice termination certificates.
#print axioms Ptx.Scalar.Mixed.Total
#print axioms Ptx.Scalar.Mixed.Total.mono
#print axioms Ptx.Scalar.Mixed.Total.scalar_next
#print axioms Ptx.Scalar.Mixed.Total.scalar_halt
#print axioms Ptx.Scalar.Mixed.Total.binary32
#print axioms Ptx.Scalar.Mixed.Total.exists_run
#print axioms Ptx.Scalar.Mixed.Total.correct
#print axioms Ptx.Scalar.Mixed.Total.prefix
#print axioms Ptx.Scalar.Mixed.Total.no_infinite
#print axioms Ptx.Scalar.Dot.Fold
#print axioms Ptx.Scalar.Dot.pointer
#print axioms Ptx.Scalar.Dot.initI
#print axioms Ptx.Scalar.Dot.test
#print axioms Ptx.Scalar.Dot.done
#print axioms Ptx.Scalar.Dot.load
#print axioms Ptx.Scalar.Dot.multiply
#print axioms Ptx.Scalar.Dot.addition
#print axioms Ptx.Scalar.Dot.increment
#print axioms Ptx.Scalar.Dot.decrement
#print axioms Ptx.Scalar.Dot.back
#print axioms Ptx.Scalar.Dot.store
#print axioms Ptx.Scalar.Dot.exit
#print axioms Ptx.Scalar.Dot.program
#print axioms Ptx.Scalar.Dot.Stored
#print axioms Ptx.Scalar.Dot.Bounds
#print axioms Ptx.Scalar.Dot.Post
#print axioms Ptx.Scalar.Dot.initial
#print axioms Ptx.Scalar.Dot.total_loop
#print axioms Ptx.Scalar.Dot.total
#print axioms Ptx.Scalar.Dot.execution_exists
#print axioms Ptx.Scalar.Dot.correct
#print axioms Ptx.Scalar.Dot.prefix_termination
#print axioms Ptx.Scalar.Dot.no_infinite_execution
#print axioms Ptx.Scalar.Dot.memory_safe
#print axioms Ptx.Scalar.Dot.other_memory
#print axioms Ptx.Binary32.DotError.Input
#print axioms Ptx.Binary32.DotError.words
#print axioms Ptx.Binary32.DotError.step
#print axioms Ptx.Binary32.DotError.rounded
#print axioms Ptx.Binary32.DotError.ideal
#print axioms Ptx.Binary32.DotError.Safe
#print axioms Ptx.Binary32.DotError.budget
#print axioms Ptx.Binary32.DotError.ideal_cons
#print axioms Ptx.Binary32.DotError.fold_accuracy
#print axioms Ptx.Binary32.DotError.stored_accuracy
#print axioms Ptx.Scalar.Dot.Examples.cancellation
#print axioms Ptx.Scalar.Dot.Examples.reordered
#print axioms Ptx.Scalar.Dot.Examples.cancellation_result
#print axioms Ptx.Scalar.Dot.Examples.reordered_result
#print axioms Ptx.Scalar.Dot.Examples.empty_result
#print axioms Ptx.Scalar.Dot.Examples.cancellationState
#print axioms Ptx.Scalar.Dot.Examples.cancellation_execution
#print axioms Ptx.Scalar.Dot.Examples.zeroInput
#print axioms Ptx.Scalar.Dot.Examples.nonempty_numerical_domain

-- Vector neuron: graph, separately supplied execution, and numerical contracts.
#print axioms PtxTorchLean.VectorVJP.inputs
#print axioms PtxTorchLean.VectorVJP.rawGraph
#print axioms PtxTorchLean.VectorVJP.output
#print axioms PtxTorchLean.VectorVJP.graph
#print axioms PtxTorchLean.VectorVJP.affine
#print axioms PtxTorchLean.VectorVJP.scale
#print axioms PtxTorchLean.VectorVJP.sensitivities
#print axioms PtxTorchLean.VectorVJP.forward_value
#print axioms PtxTorchLean.VectorVJP.generated_vjp
#print axioms PtxTorchLean.VectorVJP.checked_result
#print axioms PtxTorchLean.VectorVJP.graph_correct_at
#print axioms PtxTorchLean.VectorVJP.sensitivities_adjoint
#print axioms PtxTorchLean.VectorKernel.words
#print axioms PtxTorchLean.VectorKernel.slot
#print axioms PtxTorchLean.VectorKernel.weight
#print axioms PtxTorchLean.VectorKernel.input
#print axioms PtxTorchLean.VectorKernel.dx
#print axioms PtxTorchLean.VectorKernel.dw
#print axioms PtxTorchLean.VectorKernel.pairs
#print axioms PtxTorchLean.VectorKernel.Gradient
#print axioms PtxTorchLean.VectorKernel.Gradient.source
#print axioms PtxTorchLean.VectorKernel.Gradient.dest
#print axioms PtxTorchLean.VectorKernel.Stage
#print axioms PtxTorchLean.VectorKernel.Stage.dest
#print axioms PtxTorchLean.VectorKernel.Stage.args
#print axioms PtxTorchLean.VectorKernel.Stage.program
#print axioms PtxTorchLean.VectorKernel.arguments
#print axioms PtxTorchLean.VectorKernel.registers
#print axioms PtxTorchLean.VectorKernel.stageStart
#print axioms PtxTorchLean.VectorKernel.request
#print axioms PtxTorchLean.VectorKernel.Results
#print axioms PtxTorchLean.VectorKernel.Evaluation
#print axioms PtxTorchLean.VectorKernel.forwardStages
#print axioms PtxTorchLean.VectorKernel.gradients
#print axioms PtxTorchLean.VectorKernel.backwardStages
#print axioms PtxTorchLean.VectorKernel.words_length
#print axioms PtxTorchLean.VectorKernel.words_get
#print axioms PtxTorchLean.VectorKernel.words_getBang
#print axioms PtxTorchLean.VectorKernel.words_update
#print axioms PtxTorchLean.VectorKernel.run_correct
#print axioms PtxTorchLean.VectorKernel.run_exists
#print axioms PtxTorchLean.VectorKernel.launch_correct
#print axioms PtxTorchLean.VectorKernel.launch_exists
#print axioms PtxTorchLean.VectorKernel.pipeline_correct
#print axioms PtxTorchLean.VectorKernel.pipeline_exists
#print axioms PtxTorchLean.VectorKernel.launch_memory_safe
#print axioms PtxTorchLean.VectorKernel.pipeline_frame
#print axioms PtxTorchLean.VectorKernel.Evaluation.frame
#print axioms PtxTorchLean.VectorKernel.Gradient.source_ne_slot
#print axioms PtxTorchLean.VectorKernel.Gradient.dest_ne_slot
#print axioms PtxTorchLean.VectorKernel.Gradient.source_ne_dest
#print axioms PtxTorchLean.VectorKernel.Gradient.dest_injective
#print axioms PtxTorchLean.VectorKernel.Evaluation.sources_frame
#print axioms PtxTorchLean.VectorKernel.Evaluation.constants_frame
#print axioms PtxTorchLean.VectorKernel.forward_launches
#print axioms PtxTorchLean.VectorKernel.backward_launches
#print axioms PtxTorchLean.VectorKernel.gradient_values
#print axioms PtxTorchLean.VectorKernel.gradient_header
#print axioms PtxTorchLean.VectorKernel.gradient_mem
#print axioms PtxTorchLean.VectorKernel.forward_values
#print axioms PtxTorchLean.VectorKernel.backward_values
#print axioms PtxTorchLean.VectorKernel.one_real
#print axioms PtxTorchLean.VectorKernel.Inputs
#print axioms PtxTorchLean.VectorKernel.Inputs.x
#print axioms PtxTorchLean.VectorKernel.Inputs.w
#print axioms PtxTorchLean.VectorKernel.Inputs.dot
#print axioms PtxTorchLean.VectorKernel.Inputs.dotBudget
#print axioms PtxTorchLean.VectorKernel.Inputs.idealDot
#print axioms PtxTorchLean.VectorKernel.Inputs.affine
#print axioms PtxTorchLean.VectorKernel.Inputs.budget
#print axioms PtxTorchLean.VectorKernel.Inputs.graph_affine
#print axioms PtxTorchLean.VectorKernel.Inputs.dot_facts
#print axioms PtxTorchLean.VectorKernel.Inputs.affine_facts
#print axioms PtxTorchLean.VectorKernel.forward_accuracy
#print axioms PtxTorchLean.VectorKernel.BackwardInputs
#print axioms PtxTorchLean.VectorKernel.BackwardInputs.actualGate
#print axioms PtxTorchLean.VectorKernel.BackwardInputs.idealGate
#print axioms PtxTorchLean.VectorKernel.BackwardInputs.dxBudget
#print axioms PtxTorchLean.VectorKernel.BackwardInputs.dwBudget
#print axioms PtxTorchLean.VectorKernel.BackwardInputs.dxValue
#print axioms PtxTorchLean.VectorKernel.BackwardInputs.dwValue
#print axioms PtxTorchLean.VectorKernel.BackwardAccuracy
#print axioms PtxTorchLean.VectorKernel.backward_accuracy
#print axioms PtxTorchLean.VectorKernel.BackwardInputs.generated
#print axioms PtxTorchLean.VectorKernel.stored_forward_accuracy
#print axioms PtxTorchLean.VectorKernel.stored_backward_accuracy
#print axioms PtxTorchLean.VectorKernel.Inputs.x_coordinate
#print axioms PtxTorchLean.VectorKernel.Inputs.w_coordinate
#print axioms PtxTorchLean.VectorKernel.stored_backward_adjoint
#print axioms PtxTorchLean.VectorKernel.empty_forward
#print axioms PtxTorchLean.VectorKernel.kink_backward
#print axioms PtxTorchLean.VectorVJP.scalar
#print axioms PtxTorchLean.VectorKernel.Buffer

-- Dense graph, tree arithmetic and fetched repeated-barrier foundations.
#print axioms PtxTorchLean.TensorContext.single_flatten
#print axioms PtxTorchLean.TensorContext.unflatten_single
#print axioms PtxTorchLean.TensorContext.unflatten_add
#print axioms PtxTorchLean.DenseVJP.inputs
#print axioms PtxTorchLean.DenseVJP.rawGraph
#print axioms PtxTorchLean.DenseVJP.output
#print axioms PtxTorchLean.DenseVJP.graph
#print axioms PtxTorchLean.DenseVJP.affine
#print axioms PtxTorchLean.DenseVJP.gate
#print axioms PtxTorchLean.DenseVJP.sensitivities
#print axioms PtxTorchLean.DenseVJP.forward_value
#print axioms PtxTorchLean.DenseVJP.generated_vjp
#print axioms PtxTorchLean.DenseVJP.checked_result
#print axioms PtxTorchLean.DenseVJP.graph_correct_at
#print axioms PtxTorchLean.DenseVJP.sensitivities_adjoint
#print axioms PtxTorchLean.DenseVJP.tensorToVec_get2
#print axioms PtxTorchLean.DenseVJP.affine_coordinate
#print axioms PtxTorchLean.DenseVJP.gate_coordinate
#print axioms PtxTorchLean.DenseVJP.forward_coordinate
#print axioms PtxTorchLean.DenseVJP.backward_coordinates
#print axioms PtxTorchLean.DenseVJP.empty_input_forward
#print axioms PtxTorchLean.DenseVJP.empty_output_dx
#print axioms PtxTorchLean.DenseVJP.gate_at_zero
#print axioms Ptx.Binary32.Reduction.Tree
#print axioms Ptx.Binary32.Reduction.Tree.map
#print axioms Ptx.Binary32.Reduction.Tree.leaves
#print axioms Ptx.Binary32.Reduction.Tree.depth
#print axioms Ptx.Binary32.Reduction.balanced
#print axioms Ptx.Binary32.Reduction.balanced_depth
#print axioms Ptx.Binary32.Reduction.balanced_leaves
#print axioms Ptx.Binary32.Reduction.Eval
#print axioms Ptx.Binary32.Reduction.eval_exists
#print axioms Ptx.Binary32.Reduction.ideal
#print axioms Ptx.Binary32.Reduction.rounded
#print axioms Ptx.Binary32.Reduction.Safe
#print axioms Ptx.Binary32.Reduction.budget
#print axioms Ptx.Binary32.Reduction.words
#print axioms Ptx.Binary32.Reduction.accuracy
#print axioms Ptx.Binary32.Reduction.ideal_leaves
#print axioms Ptx.Binary32.Reduction.RowInput
#print axioms Ptx.Binary32.Reduction.RowInput.affine
#print axioms Ptx.Binary32.Reduction.RowInput.idealAffine
#print axioms Ptx.Binary32.Reduction.RowInput.error
#print axioms Ptx.Binary32.Reduction.RowEval
#print axioms Ptx.Binary32.Reduction.row_eval_exists
#print axioms Ptx.Binary32.Reduction.row_affine_accuracy
#print axioms Ptx.Binary32.Reduction.row_forward_accuracy
#print axioms Ptx.Binary32.Reduction.row_gate_accuracy
#print axioms Ptx.Scalar.Parallel.Space
#print axioms Ptx.Scalar.Parallel.Instr
#print axioms Ptx.Scalar.Parallel.Config
#print axioms Ptx.Scalar.Parallel.Lane
#print axioms Ptx.Scalar.Parallel.State
#print axioms Ptx.Scalar.Parallel.Event
#print axioms Ptx.Scalar.Parallel.Status
#print axioms Ptx.Scalar.Parallel.Outcome
#print axioms Ptx.Scalar.Parallel.setLane
#print axioms Ptx.Scalar.Parallel.arena
#print axioms Ptx.Scalar.Parallel.scalarStep
#print axioms Ptx.Scalar.Parallel.barrierConfig
#print axioms Ptx.Scalar.Parallel.barrierRequest
#print axioms Ptx.Scalar.Parallel.synchronize
#print axioms Ptx.Scalar.Parallel.Dispatch
#print axioms Ptx.Scalar.Parallel.Step
#print axioms Ptx.Scalar.Parallel.Runs
#print axioms Ptx.Scalar.Parallel.dispatch_exists
#print axioms Ptx.Scalar.Parallel.step_exists
#print axioms Ptx.Scalar.Parallel.waiting_blocks
#print axioms Ptx.Scalar.Parallel.fetch_origin
#print axioms Ptx.Scalar.Parallel.Aligned
#print axioms Ptx.Scalar.Parallel.release_aligned
#print axioms Ptx.Scalar.Parallel.reset_aligned
#print axioms Ptx.Scalar.Parallel.setLane_aligned
#print axioms Ptx.Scalar.Parallel.synchronize_aligned
#print axioms Ptx.Scalar.Parallel.dispatch_aligned
#print axioms Ptx.Scalar.Parallel.step_aligned
#print axioms Ptx.Scalar.Parallel.runs_aligned
#print axioms Ptx.Scalar.Parallel.AccessSafe
#print axioms Ptx.Scalar.Parallel.OutcomeSafe
#print axioms Ptx.Scalar.Parallel.scalarStep_safe
#print axioms Ptx.Scalar.Parallel.synchronize_safe
#print axioms Ptx.Scalar.Parallel.dispatch_safe
#print axioms Ptx.Scalar.Parallel.step_safe
#print axioms Ptx.Scalar.Parallel.runs_memory_length
#print axioms Ptx.Scalar.Parallel.runs_access_safe
#print axioms Ptx.Scalar.Parallel.afterRound
#print axioms Ptx.Scalar.Parallel.roundPrefix
#print axioms Ptx.Scalar.Parallel.runs_append
#print axioms Ptx.Scalar.Parallel.barrier_round_exists
#print axioms Ptx.Scalar.Parallel.two_barriers_exist
#print axioms PtxTorchLean.DenseVJP.column
#print axioms PtxTorchLean.DenseVJP.matrix

-- Actual repeated-barrier histories, memory projection and computed publication.
#print axioms Ptx.Scalar.Parallel.History.activeKey
#print axioms Ptx.Scalar.Parallel.History.WaitingOrigin
#print axioms Ptx.Scalar.Parallel.History.CompleteOrigins
#print axioms Ptx.Scalar.Parallel.History.FreshCompletions
#print axioms Ptx.Scalar.Parallel.History.step_history
#print axioms Ptx.Scalar.Parallel.History.runs_history
#print axioms Ptx.Scalar.Parallel.History.completed_arrivals
#print axioms Ptx.Scalar.Parallel.History.Phase
#print axioms Ptx.Scalar.Parallel.History.arrivalPosition
#print axioms Ptx.Scalar.Parallel.History.arrival_position_spec
#print axioms Ptx.Scalar.Parallel.History.certificate
#print axioms Ptx.Scalar.Parallel.History.before_certificate
#print axioms Ptx.Scalar.Parallel.History.after_certificate
#print axioms Ptx.Scalar.Parallel.Memory.slot
#print axioms Ptx.Scalar.Parallel.Memory.location
#print axioms Ptx.Scalar.Parallel.Memory.spaces_distinct
#print axioms Ptx.Scalar.Parallel.Memory.ofEffect
#print axioms Ptx.Scalar.Parallel.Memory.access
#print axioms Ptx.Scalar.Parallel.Memory.access_origin
#print axioms Ptx.Scalar.Parallel.Memory.labels
#print axioms Ptx.Scalar.Parallel.Memory.graph
#print axioms Ptx.Scalar.Parallel.Memory.labels_unique
#print axioms Ptx.Scalar.Parallel.Memory.labels_origin
#print axioms Ptx.Scalar.Parallel.Memory.step_access_complete
#print axioms Ptx.Scalar.Parallel.Memory.run_access_complete
#print axioms Ptx.Scalar.Parallel.Memory.owner
#print axioms Ptx.Scalar.Parallel.Memory.owner_program
#print axioms Ptx.Scalar.Parallel.Memory.order
#print axioms Ptx.Scalar.Parallel.Memory.read_from_unique_writer
#print axioms Ptx.Scalar.Parallel.Memory.run_memory_has_space
#print axioms Ptx.Scalar.Parallel.Memory.run_graph_complete
#print axioms Ptx.Scalar.Parallel.Memory.program_write_origin
#print axioms Ptx.Scalar.Parallel.Memory.runOrder
#print axioms Ptx.Scalar.Parallel.Memory.run_read_from_unique_writer
#print axioms Ptx.Scalar.Parallel.Reference.binary32
#print axioms Ptx.Scalar.Parallel.Reference.binary32_sound
#print axioms Ptx.Scalar.Parallel.Reference.dispatch
#print axioms Ptx.Scalar.Parallel.Reference.dispatch_sound
#print axioms Ptx.Scalar.Parallel.Reference.step
#print axioms Ptx.Scalar.Parallel.Reference.step_sound
#print axioms Ptx.Scalar.Parallel.Reference.run
#print axioms Ptx.Scalar.Parallel.Reference.run_sound
#print axioms Ptx.Scalar.Parallel.Publication.config
#print axioms Ptx.Scalar.Parallel.Publication.program
#print axioms Ptx.Scalar.Parallel.Publication.initial
#print axioms Ptx.Scalar.Parallel.Publication.schedule
#print axioms Ptx.Scalar.Parallel.Publication.execution
#print axioms Ptx.Scalar.Parallel.Publication.execution_sound
#print axioms Ptx.Scalar.Parallel.Publication.completed
#print axioms Ptx.Scalar.Parallel.Publication.successful
#print axioms Ptx.Scalar.Parallel.Publication.labels
#print axioms Ptx.Scalar.Parallel.Publication.labels_actual
#print axioms Ptx.Scalar.Parallel.Publication.source
#print axioms Ptx.Scalar.Parallel.Publication.rank
#print axioms Ptx.Scalar.Parallel.Publication.coherent
#print axioms Ptx.Scalar.Parallel.Publication.graph
#print axioms Ptx.Scalar.Parallel.Publication.order
#print axioms Ptx.Scalar.Parallel.Publication.serial_certificate
#print axioms Ptx.Scalar.Parallel.Publication.admitted
#print axioms Ptx.Scalar.Parallel.Publication.grounded
#print axioms Ptx.Scalar.Parallel.Publication.graph_actual
#print axioms Ptx.Scalar.Parallel.Publication.admitted_execution
#print axioms Ptx.Scalar.Parallel.Publication.memory_safe
#print axioms Ptx.Scalar.Parallel.Memory.Prior.initial
#print axioms Ptx.Scalar.Parallel.Memory.Prior.initial_unique
#print axioms Ptx.Scalar.Parallel.Memory.Prior.memoryKind
#print axioms Ptx.Scalar.Parallel.Memory.Prior.eval_effect_origin

-- Concrete dense program, bounded addresses, actual product phase, and software checks.
#print axioms Ptx.Scalar.Parallel.Dense.Shape
#print axioms Ptx.Scalar.Parallel.Dense.Shape.width
#print axioms Ptx.Scalar.Parallel.Dense.Shape.threads
#print axioms Ptx.Scalar.Parallel.Dense.Shape.weightBase
#print axioms Ptx.Scalar.Parallel.Dense.Shape.biasBase
#print axioms Ptx.Scalar.Parallel.Dense.Shape.outputBase
#print axioms Ptx.Scalar.Parallel.Dense.Shape.globalWords
#print axioms Ptx.Scalar.Parallel.Dense.Shape.sharedWords
#print axioms Ptx.Scalar.Parallel.Dense.Shape.thread
#print axioms Ptx.Scalar.Parallel.Dense.Shape.weight
#print axioms Ptx.Scalar.Parallel.Dense.Shape.scratch
#print axioms Ptx.Scalar.Parallel.Dense.width_positive
#print axioms Ptx.Scalar.Parallel.Dense.thread_bound
#print axioms Ptx.Scalar.Parallel.Dense.thread_injective
#print axioms Ptx.Scalar.Parallel.Dense.weight_bound
#print axioms Ptx.Scalar.Parallel.Dense.global_slices
#print axioms Ptx.Scalar.Parallel.Dense.scratch_bound
#print axioms Ptx.Scalar.Parallel.Dense.scratch_injective
#print axioms Ptx.Scalar.Parallel.Dense.children_bound
#print axioms Ptx.Scalar.Parallel.Dense.word
#print axioms Ptx.Scalar.Parallel.Dense.scalar
#print axioms Ptx.Scalar.Parallel.Dense.guarded
#print axioms Ptx.Scalar.Parallel.Dense.pointer
#print axioms Ptx.Scalar.Parallel.Dense.products
#print axioms Ptx.Scalar.Parallel.Dense.round
#print axioms Ptx.Scalar.Parallel.Dense.output
#print axioms Ptx.Scalar.Parallel.Dense.program
#print axioms Ptx.Scalar.Parallel.Dense.Bounds
#print axioms Ptx.Scalar.Parallel.Dense.config
#print axioms Ptx.Scalar.Parallel.Dense.initial
#print axioms Ptx.Scalar.Parallel.Dense.products_length
#print axioms Ptx.Scalar.Parallel.Dense.round_length
#print axioms Ptx.Scalar.Parallel.Dense.output_length
#print axioms Ptx.Scalar.Parallel.Dense.program_length
#print axioms Ptx.Scalar.Parallel.Dense.round_barrier
#print axioms Ptx.Scalar.Parallel.Dense.product_barrier
#print axioms Ptx.Scalar.Parallel.Dense.output_exit
#print axioms Ptx.Scalar.Parallel.Dense.relu_bits
#print axioms Ptx.Scalar.Parallel.Dense.thread_fits
#print axioms Ptx.Scalar.Parallel.Dense.width_fits
#print axioms Ptx.Scalar.Parallel.Dense.coordinates
#print axioms Ptx.Scalar.Parallel.Dense.decoded_coordinates
#print axioms Ptx.Scalar.Parallel.Dense.bytePointer
#print axioms Ptx.Scalar.Parallel.Dense.pointer_index
#print axioms Ptx.Scalar.Parallel.Dense.pointer_arithmetic
#print axioms Ptx.Scalar.Parallel.Dense.global_output_disjoint
#print axioms Ptx.Scalar.Parallel.Segment
#print axioms Ptx.Scalar.Parallel.Fetches
#print axioms Ptx.Scalar.Parallel.fetches_head
#print axioms Ptx.Scalar.Parallel.fetches_tail
#print axioms Ptx.Scalar.Parallel.Segment.frame
#print axioms Ptx.Scalar.Parallel.Segment.compile
#print axioms Ptx.Scalar.Parallel.Segment.append
#print axioms Ptx.Scalar.Parallel.segmentReference
#print axioms Ptx.Scalar.Parallel.SegmentRegular
#print axioms Ptx.Scalar.Parallel.segmentReference_sound
#print axioms Ptx.Scalar.Parallel.segmentReference_append
#print axioms Ptx.Scalar.Parallel.segmentRegular_append
#print axioms Ptx.Scalar.Parallel.fetches_slice
#print axioms Ptx.Scalar.Parallel.Dense.afterPointer
#print axioms Ptx.Scalar.Parallel.Dense.pointer_execution
#print axioms Ptx.Scalar.Parallel.Dense.afterSetup
#print axioms Ptx.Scalar.Parallel.Dense.setup_execution
#print axioms Ptx.Scalar.Parallel.Dense.afterLoad
#print axioms Ptx.Scalar.Parallel.Dense.guarded_load_execution
#print axioms Ptx.Scalar.Parallel.Dense.afterStore
#print axioms Ptx.Scalar.Parallel.Dense.guarded_store_execution
#print axioms Ptx.Scalar.Parallel.Dense.binary32_regular
#print axioms Ptx.Scalar.Parallel.Dense.operands
#print axioms Ptx.Scalar.Parallel.Dense.nodeValue
#print axioms Ptx.Scalar.Parallel.Dense.affineWord
#print axioms Ptx.Scalar.Parallel.Dense.forwardWord
#print axioms Ptx.Scalar.Parallel.Dense.node_tree
#print axioms Ptx.Scalar.Parallel.Dense.forward_accuracy
#print axioms Ptx.Scalar.Parallel.Dense.weight_index_fits
#print axioms Ptx.Scalar.Parallel.Dense.productFinish
#print axioms Ptx.Scalar.Parallel.Dense.product_segment
#print axioms Ptx.Scalar.Parallel.Dense.products_fetch
#print axioms Ptx.Scalar.Parallel.Dense.product_run
#print axioms Ptx.Scalar.Parallel.Dense.product_memory
#print axioms Ptx.Scalar.Parallel.Dense.product_control
#print axioms Ptx.Scalar.Parallel.Dense.ProductInvariant
#print axioms Ptx.Scalar.Parallel.Dense.product_invariant_step
#print axioms Ptx.Scalar.Parallel.Dense.product_phase_exists
#print axioms Ptx.Scalar.Parallel.Dense.Checks.schedule
#print axioms Ptx.Scalar.Parallel.Dense.Checks.seeds
#print axioms Ptx.Scalar.Parallel.Dense.Checks.check
#print axioms Ptx.Scalar.Parallel.Dense.Checks.run

-- Complete selected dense forward execution and conditional stored-word accuracy.
#print axioms Ptx.Scalar.Parallel.Dense.leftIndex
#print axioms Ptx.Scalar.Parallel.Dense.nextIndex
#print axioms Ptx.Scalar.Parallel.Dense.round_indices
#print axioms Ptx.Scalar.Parallel.Dense.round_regular
#print axioms Ptx.Scalar.Parallel.Dense.roundFinish
#print axioms Ptx.Scalar.Parallel.Dense.round_effect
#print axioms Ptx.Scalar.Parallel.Dense.program_round_split
#print axioms Ptx.Scalar.Parallel.Dense.round_fetch
#print axioms Ptx.Scalar.Parallel.Dense.round_run
#print axioms Ptx.Scalar.Parallel.Dense.PlaneReady
#print axioms Ptx.Scalar.Parallel.Dense.thread_coordinates
#print axioms Ptx.Scalar.Parallel.Dense.RoundInvariant
#print axioms Ptx.Scalar.Parallel.Dense.round_reads
#print axioms Ptx.Scalar.Parallel.Dense.round_invariant_step
#print axioms Ptx.Scalar.Parallel.Dense.round_phase_exists
#print axioms Ptx.Scalar.Parallel.Dense.first_plane_exists
#print axioms Ptx.Scalar.Parallel.Dense.reduction_exists
#print axioms Ptx.Scalar.Parallel.Dense.rootIndex
#print axioms Ptx.Scalar.Parallel.Dense.biasIndex
#print axioms Ptx.Scalar.Parallel.Dense.outputIndex
#print axioms Ptx.Scalar.Parallel.Dense.output_indices
#print axioms Ptx.Scalar.Parallel.Dense.outputFinish
#print axioms Ptx.Scalar.Parallel.Dense.outputValue
#print axioms Ptx.Scalar.Parallel.Dense.output_regular
#print axioms Ptx.Scalar.Parallel.Dense.output_effect
#print axioms Ptx.Scalar.Parallel.Dense.outputDone
#print axioms Ptx.Scalar.Parallel.Dense.output_fetch
#print axioms Ptx.Scalar.Parallel.Dense.output_run
#print axioms Ptx.Scalar.Parallel.Dense.OutputInvariant
#print axioms Ptx.Scalar.Parallel.Dense.output_value
#print axioms Ptx.Scalar.Parallel.Dense.output_invariant_step
#print axioms Ptx.Scalar.Parallel.Dense.output_phase_exists
#print axioms Ptx.Scalar.Parallel.Dense.selected_forward_exists
#print axioms Ptx.Scalar.Parallel.Dense.selected_forward_accuracy
#print axioms Ptx.Scalar.Parallel.Dense.product_coordinates

-- Concrete-read witnesses, checked replay and actual read origins.
#print axioms Ptx.Scalar.Parallel.ConcreteRuns
#print axioms Ptx.Scalar.Parallel.ConcreteRuns.toRuns
#print axioms Ptx.Scalar.Parallel.concrete_runs_append
#print axioms Ptx.Scalar.Parallel.Replay.Arrays
#print axioms Ptx.Scalar.Parallel.Replay.arrays
#print axioms Ptx.Scalar.Parallel.Replay.effect
#print axioms Ptx.Scalar.Parallel.Replay.event
#print axioms Ptx.Scalar.Parallel.Replay.trace
#print axioms Ptx.Scalar.Parallel.Replay.trace_append
#print axioms Ptx.Scalar.Parallel.Replay.eval_replays
#print axioms Ptx.Scalar.Parallel.Replay.scalar_replays
#print axioms Ptx.Scalar.Parallel.Replay.barriers_replay
#print axioms Ptx.Scalar.Parallel.Replay.dispatch_replays
#print axioms Ptx.Scalar.Parallel.Replay.step_replays
#print axioms Ptx.Scalar.Parallel.Replay.concrete_replays
#print axioms Ptx.Scalar.Parallel.Replay.reject_wrong_load
#print axioms Ptx.Scalar.Parallel.Replay.arena
#print axioms Ptx.Scalar.Parallel.Replay.writtenAt
#print axioms Ptx.Scalar.Parallel.Replay.latestWrite
#print axioms Ptx.Scalar.Parallel.Replay.latestWrite_none
#print axioms Ptx.Scalar.Parallel.Replay.latestWrite_origin
#print axioms Ptx.Scalar.Parallel.Replay.event_value
#print axioms Ptx.Scalar.Parallel.Replay.trace_value
#print axioms Ptx.Scalar.Parallel.Replay.load_prefix
#print axioms Ptx.Scalar.Parallel.Replay.load_source
#print axioms Ptx.Scalar.Parallel.Replay.ReadOrigins
#print axioms Ptx.Scalar.Parallel.Replay.read_origins
#print axioms Ptx.Scalar.Parallel.Replay.writtenAt_some
#print axioms Ptx.Scalar.Parallel.Dense.selected_forward_checked
#print axioms Ptx.Scalar.Parallel.barrier_round_concrete
#print axioms Ptx.Scalar.Parallel.ConcreteSegment
#print axioms Ptx.Scalar.Parallel.ConcreteSegment.toSegment
#print axioms Ptx.Scalar.Parallel.ConcreteSegment.frame
#print axioms Ptx.Scalar.Parallel.ConcreteSegment.append
#print axioms Ptx.Scalar.Parallel.ConcreteSegment.compile
#print axioms Ptx.Scalar.Parallel.segmentReference_concrete
#print axioms Ptx.Scalar.Parallel.Dense.selected_forward_concrete

-- Chronological graph construction and admitted dense forward execution.
#print axioms Ptx.Scalar.Parallel.Memory.Chronology.rank
#print axioms Ptx.Scalar.Parallel.Memory.Chronology.program_origin
#print axioms Ptx.Scalar.Parallel.Memory.Chronology.initial_origin
#print axioms Ptx.Scalar.Parallel.Memory.Chronology.initial_bound
#print axioms Ptx.Scalar.Parallel.Memory.Chronology.initial_rank
#print axioms Ptx.Scalar.Parallel.Memory.Chronology.program_same_position
#print axioms Ptx.Scalar.Parallel.Memory.Chronology.rank_injective
#print axioms Ptx.Scalar.Parallel.Memory.Chronology.program_before
#print axioms Ptx.Scalar.Parallel.Memory.Chronology.initial_iff
#print axioms Ptx.Scalar.Parallel.Memory.Chronology.no_release
#print axioms Ptx.Scalar.Parallel.Memory.Chronology.initial_position
#print axioms Ptx.Scalar.Parallel.Memory.Chronology.initial_before
#print axioms Ptx.Scalar.Parallel.Memory.Chronology.base_before
#print axioms Ptx.Scalar.Parallel.Memory.Chronology.split_at
#print axioms Ptx.Scalar.Parallel.Memory.Chronology.initial_member
#print axioms Ptx.Scalar.Parallel.Memory.Chronology.initial_graph_member
#print axioms Ptx.Scalar.Parallel.Memory.Chronology.writtenAt_of_address
#print axioms Ptx.Scalar.Parallel.Memory.Chronology.SourceFor
#print axioms Ptx.Scalar.Parallel.Memory.Chronology.source_exists
#print axioms Ptx.Scalar.Parallel.Memory.Chronology.chosenSource
#print axioms Ptx.Scalar.Parallel.Memory.Chronology.chronologicalCoherence
#print axioms Ptx.Scalar.Parallel.Memory.Chronology.chosenSource_spec
#print axioms Ptx.Scalar.Parallel.Memory.Chronology.concrete_certificate
#print axioms Ptx.Scalar.Parallel.Memory.Chronology.concrete_admitted
#print axioms Ptx.Scalar.Parallel.Dense.selected_forward_admitted

-- Zero padding and the admitted forward connection to the actual tensor graph.
#print axioms Ptx.Binary32.Reduction.zeroInput
#print axioms Ptx.Binary32.Reduction.paddedInput
#print axioms Ptx.Binary32.Reduction.map_balanced
#print axioms Ptx.Binary32.Reduction.balanced_ideal
#print axioms Ptx.Binary32.Reduction.padded_ideal
#print axioms PtxTorchLean.DenseForward.Encoding
#print axioms PtxTorchLean.DenseForward.Encoding.row
#print axioms PtxTorchLean.DenseForward.Encoding.row_words
#print axioms PtxTorchLean.DenseForward.Encoding.row_ideal
#print axioms PtxTorchLean.DenseForward.forward_word_accuracy
#print axioms PtxTorchLean.DenseForward.selected_forward

-- Arbitrary candidate control order, actual completion timing and dense store sites.
#print axioms Ptx.Scalar.Parallel.Control.StraightOp
#print axioms Ptx.Scalar.Parallel.Control.StraightInstr
#print axioms Ptx.Scalar.Parallel.Control.Straight
#print axioms Ptx.Scalar.Parallel.Control.stamp
#print axioms Ptx.Scalar.Parallel.Control.cursor
#print axioms Ptx.Scalar.Parallel.Control.cursor_bounds
#print axioms Ptx.Scalar.Parallel.Control.Progress
#print axioms Ptx.Scalar.Parallel.Control.dispatch_progress
#print axioms Ptx.Scalar.Parallel.Control.step_progress
#print axioms Ptx.Scalar.Parallel.Control.TraceProgress
#print axioms Ptx.Scalar.Parallel.Control.runs_progress
#print axioms Ptx.Scalar.Parallel.Control.same_site_unique
#print axioms Ptx.Scalar.Parallel.Control.position_iff_pc
#print axioms Ptx.Scalar.Parallel.Control.dispatch_completion
#print axioms Ptx.Scalar.Parallel.Control.step_completion
#print axioms Ptx.Scalar.Parallel.Control.completion_split
#print axioms Ptx.Scalar.Parallel.Control.completion_orders_sites
#print axioms Ptx.Scalar.Parallel.Control.site_after_completion
#print axioms Ptx.Scalar.Parallel.Control.completed_sites_ordered
#print axioms Ptx.Scalar.Parallel.Control.completion_site_unique
#print axioms Ptx.Scalar.Parallel.Memory.run_read_from_unique_writer_sites
#print axioms Ptx.Scalar.Parallel.Dense.program_straight
#print axioms Ptx.Scalar.Parallel.Dense.scalar_site_unique
#print axioms Ptx.Scalar.Parallel.Dense.scalar_before_arrival
#print axioms Ptx.Scalar.Parallel.Dense.scalar_after_completion
#print axioms Ptx.Scalar.Parallel.Dense.fetched_store_site
#print axioms Ptx.Scalar.Parallel.Dense.trace_store_site

-- Computed-address ownership for arbitrary candidate dense forward traces.
#print axioms Ptx.Scalar.Parallel.AddressControl.Visible
#print axioms Ptx.Scalar.Parallel.AddressControl.Agree
#print axioms Ptx.Scalar.Parallel.AddressControl.advance
#print axioms Ptx.Scalar.Parallel.AddressControl.scalar
#print axioms Ptx.Scalar.Parallel.AddressControl.instruction
#print axioms Ptx.Scalar.Parallel.AddressControl.Known
#print axioms Ptx.Scalar.Parallel.AddressControl.Allowed
#print axioms Ptx.Scalar.Parallel.AddressControl.Compatible
#print axioms Ptx.Scalar.Parallel.AddressControl.ProgramCompatible
#print axioms Ptx.Scalar.Parallel.AddressControl.agree_refl
#print axioms Ptx.Scalar.Parallel.AddressControl.agree_advance
#print axioms Ptx.Scalar.Parallel.AddressControl.agree_word
#print axioms Ptx.Scalar.Parallel.AddressControl.agree_word_left
#print axioms Ptx.Scalar.Parallel.AddressControl.agree_word_right
#print axioms Ptx.Scalar.Parallel.AddressControl.agree_address
#print axioms Ptx.Scalar.Parallel.AddressControl.agree_predicate
#print axioms Ptx.Scalar.Parallel.AddressControl.agree_predicate_right
#print axioms Ptx.Scalar.Parallel.AddressControl.operand32_eq
#print axioms Ptx.Scalar.Parallel.AddressControl.operand64_eq
#print axioms Ptx.Scalar.Parallel.AddressControl.scalar_agrees
#print axioms Ptx.Scalar.Parallel.AddressControl.evaluate
#print axioms Ptx.Scalar.Parallel.AddressControl.atPC
#print axioms Ptx.Scalar.Parallel.AddressControl.evaluate_append
#print axioms Ptx.Scalar.Parallel.AddressControl.atPC_succ
#print axioms Ptx.Scalar.Parallel.AddressControl.scalar_pc
#print axioms Ptx.Scalar.Parallel.AddressControl.Invariant
#print axioms Ptx.Scalar.Parallel.AddressControl.dispatch_invariant
#print axioms Ptx.Scalar.Parallel.AddressControl.step_invariant
#print axioms Ptx.Scalar.Parallel.AddressControl.runs_invariant
#print axioms Ptx.Scalar.Parallel.AddressControl.step_store
#print axioms Ptx.Scalar.Parallel.AddressControl.run_store
#print axioms Ptx.Scalar.Parallel.Dense.program_address_compatible
#print axioms Ptx.Scalar.Parallel.Dense.controlSeed
#print axioms Ptx.Scalar.Parallel.Dense.initial_address_control
#print axioms Ptx.Scalar.Parallel.Dense.candidate_address_control
#print axioms Ptx.Scalar.Parallel.Dense.ControlCoordinates
#print axioms Ptx.Scalar.Parallel.Dense.products_control_coordinates
#print axioms Ptx.Scalar.Parallel.Dense.round_control_coordinates
#print axioms Ptx.Scalar.Parallel.Dense.rounds_control_coordinates
#print axioms Ptx.Scalar.Parallel.Dense.product_control_address
#print axioms Ptx.Scalar.Parallel.Dense.round_control_address
#print axioms Ptx.Scalar.Parallel.Dense.output_control_address
#print axioms Ptx.Scalar.Parallel.Dense.candidate_store_address
#print axioms Ptx.Scalar.Parallel.Dense.sharedStorePC
#print axioms Ptx.Scalar.Parallel.Dense.candidate_shared_owner
#print axioms Ptx.Scalar.Parallel.Dense.candidate_global_owner
#print axioms Ptx.Scalar.Parallel.Dense.shared_store_unique
#print axioms Ptx.Scalar.Parallel.Dense.global_store_unique
#print axioms Ptx.Scalar.Parallel.Dense.candidate_store_unique
#print axioms Ptx.Scalar.Parallel.Dense.graph_writer_unique

-- Actual producers and barrier completions in arbitrary finished dense executions.
#print axioms Ptx.Scalar.Parallel.Dense.control_atPC_slice
#print axioms Ptx.Scalar.Parallel.Dense.round_control_active
#print axioms Ptx.Scalar.Parallel.Control.dispatch_pc_bound
#print axioms Ptx.Scalar.Parallel.Control.step_pc_bound
#print axioms Ptx.Scalar.Parallel.Control.crossing_step
#print axioms Ptx.Scalar.Parallel.Control.memory_crossing
#print axioms Ptx.Scalar.Parallel.Control.barrier_crossing
#print axioms Ptx.Scalar.Parallel.Control.crossed_barrier_exists
#print axioms Ptx.Scalar.Parallel.Control.halted_exit_origin
#print axioms Ptx.Scalar.Parallel.Dense.fetched_exit_site
#print axioms Ptx.Scalar.Parallel.Dense.completed_pc_bound
#print axioms Ptx.Scalar.Parallel.Dense.completed_barrier_exists
#print axioms Ptx.Scalar.Parallel.Dense.completed_phases
#print axioms Ptx.Scalar.Parallel.Dense.completed_product_store
#print axioms Ptx.Scalar.Parallel.Dense.completed_round_store
#print axioms Ptx.Scalar.Parallel.Dense.completed_output_store
#print axioms Ptx.Scalar.Parallel.Dense.completed_product_publication
#print axioms Ptx.Scalar.Parallel.Dense.completed_round_publication

-- Universal completed dense forward execution, forced sources, and no-launch wrapper.
#print axioms Ptx.Scalar.Parallel.Dense.Node
#print axioms Ptx.Scalar.Parallel.Dense.Output
#print axioms Ptx.Scalar.Parallel.Dense.node_leaf
#print axioms Ptx.Scalar.Parallel.Dense.node_fork
#print axioms Ptx.Scalar.Parallel.Dense.Data
#print axioms Ptx.Scalar.Parallel.Dense.ReadData
#print axioms Ptx.Scalar.Parallel.Dense.StoreData
#print axioms Ptx.Scalar.Parallel.Dense.initial_data
#print axioms Ptx.Scalar.Parallel.Dense.product_fp_data
#print axioms Ptx.Scalar.Parallel.Dense.round_fp_data
#print axioms Ptx.Scalar.Parallel.Dense.output_fp_data
#print axioms Ptx.Scalar.Parallel.Dense.DataInvariant
#print axioms Ptx.Scalar.Parallel.Dense.Stores
#print axioms Ptx.Scalar.Parallel.Dense.Reads
#print axioms Ptx.Scalar.Parallel.Dense.dispatch_data
#print axioms Ptx.Scalar.Parallel.Dense.step_data
#print axioms Ptx.Scalar.Parallel.Dense.scalar_step_singleton
#print axioms Ptx.Scalar.Parallel.Dense.program_segment
#print axioms Ptx.Scalar.Parallel.Dense.scalar_data
#print axioms Ptx.Scalar.Parallel.Dense.fp_data
#print axioms Ptx.Scalar.Parallel.Dense.barrier_data
#print axioms Ptx.Scalar.Parallel.Dense.run_data
#print axioms Ptx.Scalar.Parallel.Dense.product_scalar_data
#print axioms Ptx.Scalar.Parallel.Dense.round_scalar_data
#print axioms Ptx.Scalar.Parallel.Dense.output_scalar_data
#print axioms Ptx.Scalar.Parallel.Dense.global_load_index
#print axioms Ptx.Scalar.Parallel.Dense.global_prefix_unwritten
#print axioms Ptx.Scalar.Parallel.Dense.global_read_source
#print axioms Ptx.Scalar.Parallel.Dense.launchPlan
#print axioms Ptx.Scalar.Parallel.Dense.launchPlan_empty
#print axioms Ptx.Scalar.Parallel.Dense.launchPlan_kernel
#print axioms Ptx.Scalar.Parallel.Dense.ForwardRun
#print axioms Ptx.Scalar.Parallel.Dense.empty_forward
#print axioms Ptx.Scalar.Parallel.Dense.empty_forward_unique
#print axioms Ptx.Scalar.Parallel.Dense.product_read_control
#print axioms Ptx.Scalar.Parallel.Dense.round_read_control
#print axioms Ptx.Scalar.Parallel.Dense.output_read_control
#print axioms Ptx.Scalar.Parallel.Dense.productLoad
#print axioms Ptx.Scalar.Parallel.Dense.roundLoad
#print axioms Ptx.Scalar.Parallel.Dense.outputLoad
#print axioms Ptx.Scalar.Parallel.Dense.fetched_load_site
#print axioms Ptx.Scalar.Parallel.Dense.candidate_load_address
#print axioms Ptx.Scalar.Parallel.Dense.scratch_pointer_owner
#print axioms Ptx.Scalar.Parallel.Dense.store_node
#print axioms Ptx.Scalar.Parallel.Dense.shared_load_node
#print axioms Ptx.Scalar.Parallel.Dense.read_data
#print axioms Ptx.Scalar.Parallel.Dense.Admitted
#print axioms Ptx.Scalar.Parallel.Dense.visible_store
#print axioms Ptx.Scalar.Parallel.Dense.plane_publication
#print axioms Ptx.Scalar.Parallel.Dense.child_owner
#print axioms Ptx.Scalar.Parallel.Dense.shared_read_source
#print axioms Ptx.Scalar.Parallel.Dense.scalar_store_data
#print axioms Ptx.Scalar.Parallel.Dense.completed_forward
#print axioms Ptx.Scalar.Parallel.AddressControl.step_load
#print axioms Ptx.Scalar.Parallel.AddressControl.run_load
#print axioms Ptx.Scalar.Parallel.Replay.latestWrite_append
#print axioms Ptx.Scalar.Parallel.Replay.run_value
#print axioms PtxTorchLean.DenseForward.output_accuracy
#print axioms PtxTorchLean.DenseForward.universal_forward
#print axioms PtxTorchLean.DenseForward.wrapper_forward

-- Completed parallel dense backward: stored handoffs, universal accuracy, and existence.
#print axioms Ptx.Scalar.Parallel.DenseBackward.Checks.run
#print axioms Ptx.Scalar.Parallel.DenseBackward.Shape
#print axioms Ptx.Scalar.Parallel.DenseBackward.Shape.transposed
#print axioms Ptx.Scalar.Parallel.DenseBackward.Shape.gateBase
#print axioms Ptx.Scalar.Parallel.DenseBackward.Shape.weightBase
#print axioms Ptx.Scalar.Parallel.DenseBackward.Shape.weightCount
#print axioms Ptx.Scalar.Parallel.DenseBackward.Shape.copyBase
#print axioms Ptx.Scalar.Parallel.DenseBackward.Bounds
#print axioms Ptx.Scalar.Parallel.DenseBackward.gateLayout
#print axioms Ptx.Scalar.Parallel.DenseBackward.weightLayout
#print axioms Ptx.Scalar.Parallel.DenseBackward.copySource
#print axioms Ptx.Scalar.Parallel.DenseBackward.copy_source_bound
#print axioms Ptx.Scalar.Parallel.DenseBackward.copyLayout
#print axioms Ptx.Scalar.Parallel.DenseBackward.gateInput
#print axioms Ptx.Scalar.Parallel.DenseBackward.weightInput
#print axioms Ptx.Scalar.Parallel.DenseBackward.copyInput
#print axioms Ptx.Scalar.Parallel.DenseBackward.packet
#print axioms Ptx.Scalar.Parallel.DenseBackward.Execution
#print axioms Ptx.Scalar.Parallel.DenseBackward.execution_exists
#print axioms Ptx.Scalar.Parallel.DenseBackward.Execution.g
#print axioms Ptx.Scalar.Parallel.DenseBackward.Execution.dw
#print axioms Ptx.Scalar.Parallel.DenseBackward.Execution.dx
#print axioms Ptx.Scalar.Parallel.DenseBackward.lengths
#print axioms Ptx.Scalar.Parallel.DenseBackward.input_frame
#print axioms Ptx.Scalar.Parallel.DenseBackward.gate_frame
#print axioms Ptx.Scalar.Parallel.DenseBackward.gate_result
#print axioms Ptx.Scalar.Parallel.DenseBackward.weight_result
#print axioms Ptx.Scalar.Parallel.DenseBackward.packet_word
#print axioms Ptx.Scalar.Parallel.DenseBackward.packet_input
#print axioms Ptx.Scalar.Parallel.DenseBackward.packet_weight
#print axioms Ptx.Scalar.Parallel.DenseBackward.packet_bias
#print axioms Ptx.Scalar.Parallel.DenseBackward.input_result
#print axioms Ptx.Scalar.Parallel.DenseBackward.gradients_stored
#print axioms Ptx.Scalar.Parallel.Dense.Launch
#print axioms Ptx.Scalar.Parallel.Dense.launch_exists
#print axioms Ptx.Scalar.Parallel.Dense.launch_correct
#print axioms Ptx.Scalar.Parallel.Dense.activate
#print axioms Ptx.Scalar.Parallel.Dense.activateReal
#print axioms Ptx.Scalar.Parallel.Pointwise.compatible
#print axioms Ptx.Scalar.Parallel.Pointwise.control_addresses
#print axioms Ptx.Scalar.Parallel.Pointwise.initial_control
#print axioms Ptx.Scalar.Parallel.Pointwise.initial_aligned
#print axioms Ptx.Scalar.Parallel.Pointwise.fetched_load
#print axioms Ptx.Scalar.Parallel.Pointwise.fetched_store
#print axioms Ptx.Scalar.Parallel.Pointwise.load_address
#print axioms Ptx.Scalar.Parallel.Pointwise.store_address
#print axioms Ptx.Scalar.Parallel.Pointwise.RegisterValue
#print axioms Ptx.Scalar.Parallel.Pointwise.Data
#print axioms Ptx.Scalar.Parallel.Pointwise.gate_bits
#print axioms Ptx.Scalar.Parallel.Pointwise.scalar_data
#print axioms Ptx.Scalar.Parallel.Pointwise.fp_data
#print axioms Ptx.Scalar.Parallel.Pointwise.scalar_store_data
#print axioms Ptx.Scalar.Parallel.Pointwise.Pointers
#print axioms Ptx.Scalar.Parallel.Pointwise.finish
#print axioms Ptx.Scalar.Parallel.Pointwise.lane_regular
#print axioms Ptx.Scalar.Parallel.Pointwise.lane_effect
#print axioms Ptx.Scalar.Parallel.Pointwise.done
#print axioms Ptx.Scalar.Parallel.Pointwise.lane_run
#print axioms Ptx.Scalar.Parallel.Pointwise.Progress
#print axioms Ptx.Scalar.Parallel.Pointwise.execution_exists
#print axioms Ptx.Scalar.Parallel.Pointwise.admitted_exists
#print axioms Ptx.Scalar.Parallel.Pointwise.Launch
#print axioms Ptx.Scalar.Parallel.Pointwise.launch_exists
#print axioms Ptx.Scalar.Parallel.Pointwise.launch_correct
#print axioms Ptx.Scalar.Parallel.Pointwise.launch_access_safe
#print axioms Ptx.Scalar.Parallel.Pointwise.DataInvariant
#print axioms Ptx.Scalar.Parallel.Pointwise.Stores
#print axioms Ptx.Scalar.Parallel.Pointwise.Reads
#print axioms Ptx.Scalar.Parallel.Pointwise.dispatch_data
#print axioms Ptx.Scalar.Parallel.Pointwise.step_data
#print axioms Ptx.Scalar.Parallel.Pointwise.scalar_step_singleton
#print axioms Ptx.Scalar.Parallel.Pointwise.Op
#print axioms Ptx.Scalar.Parallel.Pointwise.localOp
#print axioms Ptx.Scalar.Parallel.Pointwise.clear
#print axioms Ptx.Scalar.Parallel.Pointwise.body
#print axioms Ptx.Scalar.Parallel.Pointwise.program
#print axioms Ptx.Scalar.Parallel.Pointwise.storePC
#print axioms Ptx.Scalar.Parallel.Pointwise.Result
#print axioms Ptx.Scalar.Parallel.Pointwise.reference
#print axioms Ptx.Scalar.Parallel.Pointwise.reference_result
#print axioms Ptx.Scalar.Parallel.Pointwise.Layout
#print axioms Ptx.Scalar.Parallel.Pointwise.Layout.output
#print axioms Ptx.Scalar.Parallel.Pointwise.seed
#print axioms Ptx.Scalar.Parallel.Pointwise.initial
#print axioms Ptx.Scalar.Parallel.Pointwise.config
#print axioms Ptx.Scalar.Parallel.Pointwise.length_program
#print axioms Ptx.Scalar.Parallel.Pointwise.straight
#print axioms Ptx.Scalar.Parallel.Pointwise.Admitted
#print axioms Ptx.Scalar.Parallel.Pointwise.pointer_index
#print axioms Ptx.Scalar.Parallel.Pointwise.prefix_unwritten
#print axioms Ptx.Scalar.Parallel.Pointwise.read_source
#print axioms Ptx.Scalar.Parallel.Pointwise.run_data
#print axioms Ptx.Scalar.Parallel.Pointwise.completed_pc
#print axioms Ptx.Scalar.Parallel.Pointwise.completed_store
#print axioms Ptx.Scalar.Parallel.Pointwise.written_result
#print axioms Ptx.Scalar.Parallel.Pointwise.completed
#print axioms PtxTorchLean.DenseBackward.Encoding
#print axioms PtxTorchLean.DenseBackward.Encoding.gWord
#print axioms PtxTorchLean.DenseBackward.Encoding.gReal
#print axioms PtxTorchLean.DenseBackward.Encoding.gIdeal
#print axioms PtxTorchLean.DenseBackward.Encoding.g_real
#print axioms PtxTorchLean.DenseBackward.Encoding.affine_accuracy
#print axioms PtxTorchLean.DenseBackward.Encoding.g_error
#print axioms PtxTorchLean.DenseBackward.Encoding.g_ideal
#print axioms PtxTorchLean.DenseBackward.stored_gate
#print axioms PtxTorchLean.DenseBackward.ProductRanges
#print axioms PtxTorchLean.DenseBackward.weightEntry
#print axioms PtxTorchLean.DenseBackward.inputEntry
#print axioms PtxTorchLean.DenseBackward.inputTree
#print axioms PtxTorchLean.DenseBackward.Ranges
#print axioms PtxTorchLean.DenseBackward.inputRow
#print axioms PtxTorchLean.DenseBackward.input_words
#print axioms PtxTorchLean.DenseBackward.input_ideal
#print axioms PtxTorchLean.DenseBackward.weight_accuracy
#print axioms PtxTorchLean.DenseBackward.input_accuracy
#print axioms PtxTorchLean.DenseBackward.bias_accuracy
#print axioms PtxTorchLean.DenseBackward.Encoding.away
#print axioms PtxTorchLean.DenseBackward.Correct
#print axioms PtxTorchLean.DenseBackward.universal_backward
#print axioms PtxTorchLean.DenseBackward.backward_exists

-- Actual grid execution, pointwise existence, and conditional universal dense forward.
#print axioms Ptx.Scalar.Parallel.Dense.ArithmeticBounds
#print axioms Ptx.Scalar.Parallel.Grid.step_memory_origin
#print axioms Ptx.Scalar.Parallel.Grid.run_memory_origin
#print axioms Ptx.Scalar.Parallel.Grid.run_store
#print axioms Ptx.Scalar.Parallel.Grid.run_load
#print axioms Ptx.Scalar.Parallel.Grid.project_mem
#print axioms Ptx.Scalar.Parallel.Grid.completed_arrival
#print axioms Ptx.Scalar.Parallel.Grid.Checks.run
#print axioms Ptx.Scalar.Parallel.Grid.Control.step_completion
#print axioms Ptx.Scalar.Parallel.Grid.Control.completion_split
#print axioms Ptx.Scalar.Parallel.Grid.Control.completion_orders_sites
#print axioms Ptx.Scalar.Parallel.Grid.Control.site_after_completion
#print axioms Ptx.Scalar.Parallel.Grid.Control.completed_sites_ordered
#print axioms Ptx.Scalar.Parallel.Grid.Control.completion_site_unique
#print axioms Ptx.Scalar.Parallel.Grid.Control.stamp
#print axioms Ptx.Scalar.Parallel.Grid.Control.cursor
#print axioms Ptx.Scalar.Parallel.Grid.Control.cursor_bounds
#print axioms Ptx.Scalar.Parallel.Grid.Control.Progress
#print axioms Ptx.Scalar.Parallel.Grid.Control.step_progress
#print axioms Ptx.Scalar.Parallel.Grid.Control.TraceProgress
#print axioms Ptx.Scalar.Parallel.Grid.Control.runs_progress
#print axioms Ptx.Scalar.Parallel.Grid.Control.same_site_unique
#print axioms Ptx.Scalar.Parallel.Grid.Control.position_iff_pc
#print axioms Ptx.Scalar.Parallel.Grid.Control.step_pc_bound
#print axioms Ptx.Scalar.Parallel.Grid.Control.crossing_step
#print axioms Ptx.Scalar.Parallel.Grid.Control.crossed_barrier_exists
#print axioms Ptx.Scalar.Parallel.Grid.Control.halted_exit_origin
#print axioms Ptx.Scalar.Parallel.GridDense.candidate_store_address
#print axioms Ptx.Scalar.Parallel.GridDense.candidate_load_address
#print axioms Ptx.Scalar.Parallel.GridDense.Checks.check
#print axioms Ptx.Scalar.Parallel.GridDense.Checks.run
#print axioms Ptx.Scalar.Parallel.GridDense.Phase
#print axioms Ptx.Scalar.Parallel.GridDense.completed_pc_bound
#print axioms Ptx.Scalar.Parallel.GridDense.completed_barrier_exists
#print axioms Ptx.Scalar.Parallel.GridDense.completed_phases
#print axioms Ptx.Scalar.Parallel.GridDense.completed_product_store
#print axioms Ptx.Scalar.Parallel.GridDense.completed_round_store
#print axioms Ptx.Scalar.Parallel.GridDense.completed_output_store
#print axioms Ptx.Scalar.Parallel.GridDense.LocalData.DataInvariant
#print axioms Ptx.Scalar.Parallel.GridDense.LocalData.Stores
#print axioms Ptx.Scalar.Parallel.GridDense.LocalData.Reads
#print axioms Ptx.Scalar.Parallel.GridDense.LocalData.dispatch_data
#print axioms Ptx.Scalar.Parallel.GridDense.LocalData.step_data
#print axioms Ptx.Scalar.Parallel.GridDense.DataInvariant
#print axioms Ptx.Scalar.Parallel.GridDense.Stores
#print axioms Ptx.Scalar.Parallel.GridDense.Reads
#print axioms Ptx.Scalar.Parallel.GridDense.step_data
#print axioms Ptx.Scalar.Parallel.GridDense.scalar_step_singleton
#print axioms Ptx.Scalar.Parallel.GridDense.run_data
#print axioms Ptx.Scalar.Parallel.GridDense.global_load_index
#print axioms Ptx.Scalar.Parallel.GridDense.global_prefix_unwritten
#print axioms Ptx.Scalar.Parallel.GridDense.global_read_source
#print axioms Ptx.Scalar.Parallel.GridDense.candidate_shared_owner
#print axioms Ptx.Scalar.Parallel.GridDense.candidate_global_owner
#print axioms Ptx.Scalar.Parallel.GridDense.scalar_site_unique
#print axioms Ptx.Scalar.Parallel.GridDense.shared_store_unique
#print axioms Ptx.Scalar.Parallel.GridDense.global_store_unique
#print axioms Ptx.Scalar.Parallel.GridDense.Bounds
#print axioms Ptx.Scalar.Parallel.GridDense.config
#print axioms Ptx.Scalar.Parallel.GridDense.thread
#print axioms Ptx.Scalar.Parallel.GridDense.initial
#print axioms Ptx.Scalar.Parallel.GridDense.thread_coordinates
#print axioms Ptx.Scalar.Parallel.GridDense.thread_unique
#print axioms Ptx.Scalar.Parallel.GridDense.initial_aligned
#print axioms Ptx.Scalar.Parallel.GridDense.initial_control
#print axioms Ptx.Scalar.Parallel.GridDense.candidate_control
#print axioms Ptx.Scalar.Parallel.GridDense.scratch_pointer_owner
#print axioms Ptx.Scalar.Parallel.GridDense.store_node
#print axioms Ptx.Scalar.Parallel.GridDense.shared_load_node
#print axioms Ptx.Scalar.Parallel.GridDense.read_data
#print axioms Ptx.Scalar.Parallel.GridDense.Admitted
#print axioms Ptx.Scalar.Parallel.GridDense.visible_store
#print axioms Ptx.Scalar.Parallel.GridDense.plane_publication
#print axioms Ptx.Scalar.Parallel.GridDense.child_owner
#print axioms Ptx.Scalar.Parallel.GridDense.shared_read_source
#print axioms Ptx.Scalar.Parallel.GridDense.completed_forward
#print axioms Ptx.Scalar.Parallel.GridDense.candidate_store_unique
#print axioms Ptx.Scalar.Parallel.GridDense.graph_writer_unique
#print axioms Ptx.Scalar.Parallel.Grid.Local
#print axioms Ptx.Scalar.Parallel.Grid.State
#print axioms Ptx.Scalar.Parallel.Grid.Config
#print axioms Ptx.Scalar.Parallel.Grid.Config.group
#print axioms Ptx.Scalar.Parallel.Grid.view
#print axioms Ptx.Scalar.Parallel.Grid.localOf
#print axioms Ptx.Scalar.Parallel.Grid.install
#print axioms Ptx.Scalar.Parallel.Grid.tag
#print axioms Ptx.Scalar.Parallel.Grid.Step
#print axioms Ptx.Scalar.Parallel.Grid.Runs
#print axioms Ptx.Scalar.Parallel.Grid.view_install_same
#print axioms Ptx.Scalar.Parallel.Grid.install_local_other
#print axioms Ptx.Scalar.Parallel.Grid.view_install_other
#print axioms Ptx.Scalar.Parallel.Grid.step_exists
#print axioms Ptx.Scalar.Parallel.Grid.step_lengths
#print axioms Ptx.Scalar.Parallel.Grid.runs_lengths
#print axioms Ptx.Scalar.Parallel.Grid.AccessSafe
#print axioms Ptx.Scalar.Parallel.Grid.step_access_safe
#print axioms Ptx.Scalar.Parallel.Grid.access_safe_of_lengths
#print axioms Ptx.Scalar.Parallel.Grid.runs_access_safe
#print axioms Ptx.Scalar.Parallel.Grid.step_aligned
#print axioms Ptx.Scalar.Parallel.Grid.runs_aligned
#print axioms Ptx.Scalar.Parallel.Grid.runs_append
#print axioms Ptx.Scalar.Parallel.Grid.embed_run
#print axioms Ptx.Scalar.Parallel.Grid.flatThread
#print axioms Ptx.Scalar.Parallel.Grid.product_div
#print axioms Ptx.Scalar.Parallel.Grid.product_mod
#print axioms Ptx.Scalar.Parallel.Grid.flatten
#print axioms Ptx.Scalar.Parallel.Grid.flatEvent
#print axioms Ptx.Scalar.Parallel.Grid.flatEvents
#print axioms Ptx.Scalar.Parallel.Grid.flatten_global
#print axioms Ptx.Scalar.Parallel.Grid.view_global
#print axioms Ptx.Scalar.Parallel.Grid.view_lanes
#print axioms Ptx.Scalar.Parallel.Grid.flatten_lane
#print axioms Ptx.Scalar.Parallel.Grid.install_view
#print axioms Ptx.Scalar.Parallel.Grid.flatten_install_lane
#print axioms Ptx.Scalar.Parallel.Grid.GlobalOnly
#print axioms Ptx.Scalar.Parallel.Grid.IdleBarriers
#print axioms Ptx.Scalar.Parallel.Grid.flatten_install_global
#print axioms Ptx.Scalar.Parallel.Grid.flatOutcome
#print axioms Ptx.Scalar.Parallel.Grid.scalar_flatten
#print axioms Ptx.Scalar.Parallel.Grid.dispatch_flatten
#print axioms Ptx.Scalar.Parallel.Grid.dispatch_barrier
#print axioms Ptx.Scalar.Parallel.Grid.step_barrier
#print axioms Ptx.Scalar.Parallel.Grid.step_idle
#print axioms Ptx.Scalar.Parallel.Grid.local_step_flatten
#print axioms Ptx.Scalar.Parallel.Grid.flatten_run
#print axioms Ptx.Scalar.Parallel.Grid.Memory.threadId
#print axioms Ptx.Scalar.Parallel.Grid.Memory.owner
#print axioms Ptx.Scalar.Parallel.Grid.Memory.ofEffect
#print axioms Ptx.Scalar.Parallel.Grid.Memory.access
#print axioms Ptx.Scalar.Parallel.Grid.Memory.initials
#print axioms Ptx.Scalar.Parallel.Grid.Memory.label
#print axioms Ptx.Scalar.Parallel.Grid.Memory.labels
#print axioms Ptx.Scalar.Parallel.Grid.Memory.graph
#print axioms Ptx.Scalar.Parallel.Grid.Memory.cross
#print axioms Ptx.Scalar.Parallel.Grid.Memory.Admitted
#print axioms Ptx.Scalar.Parallel.Grid.Memory.access_complete
#print axioms Ptx.Scalar.Parallel.Grid.Memory.graph_complete
#print axioms Ptx.Scalar.Parallel.Grid.Memory.threadId_unique
#print axioms Ptx.Scalar.Parallel.Grid.Memory.cross_forward
#print axioms Ptx.Scalar.Parallel.Grid.Memory.access_origin
#print axioms Ptx.Scalar.Parallel.Grid.Memory.labels_origin
#print axioms Ptx.Scalar.Parallel.Grid.Memory.program_write_origin
#print axioms Ptx.Scalar.Parallel.Grid.Memory.initial_origin
#print axioms Ptx.Scalar.Parallel.Grid.Memory.initial_global
#print axioms Ptx.Scalar.Parallel.Grid.Memory.initials_unique
#print axioms Ptx.Scalar.Parallel.Grid.Memory.labels_unique
#print axioms Ptx.Scalar.Parallel.Grid.project
#print axioms Ptx.Scalar.Parallel.Grid.project_append
#print axioms Ptx.Scalar.Parallel.Grid.project_tag_same
#print axioms Ptx.Scalar.Parallel.Grid.project_tag_other
#print axioms Ptx.Scalar.Parallel.Grid.Origins
#print axioms Ptx.Scalar.Parallel.Grid.step_origins
#print axioms Ptx.Scalar.Parallel.Grid.runs_origins
#print axioms Ptx.Scalar.Parallel.Grid.completed_arrivals
#print axioms Ptx.Scalar.Parallel.Grid.Invariant
#print axioms Ptx.Scalar.Parallel.Grid.step_invariant
#print axioms Ptx.Scalar.Parallel.Grid.runs_invariant
#print axioms Ptx.Scalar.Parallel.Grid.runs_address_control
#print axioms Ptx.Scalar.Parallel.Grid.location
#print axioms Ptx.Scalar.Parallel.Grid.shared_private
#print axioms Ptx.Scalar.Parallel.Grid.global_shared_distinct
#print axioms Ptx.Scalar.Parallel.Grid.global_common
#print axioms Ptx.Scalar.Parallel.Grid.latestGlobal
#print axioms Ptx.Scalar.Parallel.Grid.latestGlobal_append
#print axioms Ptx.Scalar.Parallel.Grid.step_global_value
#print axioms Ptx.Scalar.Parallel.Grid.run_global_value
#print axioms Ptx.Scalar.Parallel.Grid.unchanged_global
#print axioms Ptx.Scalar.Parallel.Grid.global_frame
#print axioms Ptx.Scalar.Parallel.GridPointwise.initial
#print axioms Ptx.Scalar.Parallel.GridPointwise.initial_flatten
#print axioms Ptx.Scalar.Parallel.GridPointwise.initial_idle
#print axioms Ptx.Scalar.Parallel.GridPointwise.program_global
#print axioms Ptx.Scalar.Parallel.GridPointwise.candidate_run
#print axioms Ptx.Scalar.Parallel.GridPointwise.Admitted
#print axioms Ptx.Scalar.Parallel.GridPointwise.completed
#print axioms Ptx.Scalar.Parallel.GridPointwise.admitted_exists
#print axioms Ptx.Scalar.Parallel.GridPointwise.Launch
#print axioms Ptx.Scalar.Parallel.GridPointwise.launch_exists
#print axioms Ptx.Scalar.Parallel.GridPointwise.launch_correct
#print axioms Ptx.Scalar.Parallel.GridPointwise.groupCount
#print axioms Ptx.Scalar.Parallel.GridPointwise.capacity_bounds
#print axioms Ptx.Scalar.Parallel.GridPointwise.empty_groupCount
#print axioms Ptx.Scalar.Parallel.GridPointwise.paddedLayout
#print axioms Ptx.Scalar.Parallel.GridPointwise.padded_exists
#print axioms Ptx.Scalar.Parallel.GridPointwise.padded_correct
#print axioms Ptx.Scalar.Parallel.Grid.Reference.step
#print axioms Ptx.Scalar.Parallel.Grid.Reference.run
#print axioms Ptx.Scalar.Parallel.Grid.Reference.step_sound
#print axioms Ptx.Scalar.Parallel.Grid.Reference.run_sound
#print axioms Ptx.Scalar.Parallel.Grid.dispatch_reflect
#print axioms Ptx.Scalar.Parallel.Grid.local_step_reflect
#print axioms Ptx.Scalar.Parallel.Grid.reflect_run
#print axioms PtxTorchLean.GridDenseForward.universal_forward

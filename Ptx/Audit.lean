import Ptx

/-! Public proof dependencies, consumed by `scripts/check.sh`. -/
#print axioms Ptx.step_exists
#print axioms Ptx.step_deterministic
#print axioms Ptx.load_writes_destination
#print axioms Ptx.store_emits_operand
#print axioms Ptx.execute_runs
#print axioms Ptx.runs_eq_execute
#print axioms Ptx.runs_exists
#print axioms Ptx.runs_deterministic
#print axioms Ptx.execute_effects
#print axioms Ptx.execute_getElem?
#print axioms Ptx.execute_access_safe
#print axioms Ptx.word_footprints_disjoint
#print axioms Ptx.Program.all_threads_run
#print axioms Ptx.Program.events_origin
#print axioms Ptx.Program.graph_event_origin
#print axioms Ptx.Program.load_origin
#print axioms Ptx.Program.store_origin
#print axioms Ptx.Program.initial_origin
#print axioms Ptx.Program.no_invented_values
#print axioms Ptx.Program.admitted_access_safe
#print axioms Ptx.Graph.single_copy
#print axioms Ptx.Graph.no_source_coherence_predecessor
#print axioms Ptx.Graph.valid_of_certificate
#print axioms Ptx.MessagePassing.publication
#print axioms Ptx.MessagePassing.publication_observed
#print axioms Ptx.MessagePassing.successful_execution_exists
#print axioms Ptx.MessagePassing.relaxed_counterexample_exists
#print axioms Ptx.MessagePassing.memory_safe
#print axioms Ptx.MessagePassing.objects_disjoint
#print axioms Ptx.MessagePassing.local_completion
#print axioms Ptx.MessagePassing.acquire_stale_impossible

/-! Exact checking, complete outcomes, and the additional litmus suite. -/
#print axioms Ptx.reachable_iff
#print axioms Ptx.Graph.baseCheck_iff
#print axioms Ptx.Graph.causeCheck_iff
#print axioms Ptx.Graph.locationCheck_iff
#print axioms Ptx.Graph.check_iff
#print axioms Ptx.Graph.check_false_iff
#print axioms Ptx.MessagePassing.source_values
#print axioms Ptx.MessagePassing.acquire_outcomes
#print axioms Ptx.MessagePassing.relaxed_outcomes
#print axioms Ptx.MessagePassing.zero_flag_check
#print axioms Ptx.MessagePassing.relaxed_check
#print axioms Ptx.MessagePassing.acquire_success_check
#print axioms Ptx.MessagePassing.acquire_stale_check
#print axioms Ptx.CheckerExamples.empty_relation
#print axioms Ptx.CheckerExamples.singleton_loop
#print axioms Ptx.CheckerExamples.cycle_reachable
#print axioms Ptx.CheckerExamples.empty_graph_accepted
#print axioms Ptx.CheckerExamples.initialized_graph_accepted
#print axioms Ptx.CheckerExamples.read_cannot_source_itself
#print axioms Ptx.CheckerExamples.reflexive_coherence_rejected
#print axioms Ptx.CheckerExamples.wrong_value_rejected
#print axioms Ptx.CheckerExamples.wrong_address_rejected
#print axioms Ptx.CheckerExamples.missing_initial_coherence_rejected
#print axioms Ptx.CheckerExamples.wrong_value_invalid
#print axioms Ptx.CheckerExamples.base_cycle_detected
#print axioms Ptx.CheckerExamples.base_cycle_rejected
#print axioms Ptx.Litmus.StoreBuffering.both_zero_exists
#print axioms Ptx.Litmus.StoreBuffering.memory_safe
#print axioms Ptx.Litmus.SameLocation.ordered_read
#print axioms Ptx.Litmus.SameLocation.stale_impossible
#print axioms Ptx.Litmus.SameLocation.execution_exists
#print axioms Ptx.Litmus.SameLocation.memory_safe
#print axioms Ptx.Litmus.ReleasePair.publication_observed
#print axioms Ptx.Litmus.ReleasePair.execution_exists
#print axioms Ptx.Litmus.ReleasePair.no_direct_release_observation
#print axioms Ptx.Litmus.ReleasePair.memory_safe
#print axioms Ptx.Litmus.AcquirePair.publication_observed
#print axioms Ptx.Litmus.AcquirePair.execution_exists
#print axioms Ptx.Litmus.AcquirePair.no_direct_release_observation
#print axioms Ptx.Litmus.AcquirePair.memory_safe
#print axioms Ptx.Litmus.ReleasePair.pair_required
#print axioms Ptx.Litmus.AcquirePair.pair_required
#print axioms Ptx.Litmus.ReleasePair.witness_synchronizes
#print axioms Ptx.Litmus.AcquirePair.witness_synchronizes

/-! Explicit environments, scoped constraints, scalar execution and kernel bridges. -/

-- Environment
#print axioms Ptx.Scope.includes_self
#print axioms Ptx.Scope.cta_includes_cluster
#print axioms Ptx.Scope.cluster_includes_gpu
#print axioms Ptx.Environment.accessible_contract
#print axioms Ptx.Environment.accessible_bounds

-- ScopedMemory
#print axioms Ptx.ScopedGraph.morallyStrong_legacy
#print axioms Ptx.ScopedGraph.observation_legacy
#print axioms Ptx.ScopedGraph.sync_legacy
#print axioms Ptx.ScopedGraph.base_legacy
#print axioms Ptx.ScopedGraph.cause_legacy
#print axioms Ptx.ScopedGraph.location_legacy
#print axioms Ptx.ScopedGraph.coherent_legacy
#print axioms Ptx.ScopedGraph.valid_legacy

-- ScopedExamples
#print axioms Ptx.ScopedExamples.publication
#print axioms Ptx.ScopedExamples.gpu_all_in_scope
#print axioms Ptx.ScopedExamples.gpu_specialization
#print axioms Ptx.ScopedExamples.in_scope_execution_exists
#print axioms Ptx.ScopedExamples.outside_scope_execution_exists
#print axioms Ptx.ScopedExamples.outside_scope_no_sync
#print axioms Ptx.ScopedExamples.scope_inclusion_is_mutual
#print axioms Ptx.ScopedExamples.different_grids_not_same_cta
#print axioms Ptx.ScopedExamples.different_grids_same_gpu
#print axioms Ptx.ScopedExamples.same_cluster_different_cta
#print axioms Ptx.ScopedExamples.shared_owner_can_access
#print axioms Ptx.ScopedExamples.shared_other_cta_cannot_access
#print axioms Ptx.ScopedExamples.explicit_cluster_shared_access
#print axioms Ptx.ScopedExamples.shared_other_grid_cannot_access
#print axioms Ptx.ScopedExamples.misalignment_rejected
#print axioms Ptx.ScopedExamples.bounds_rejected
#print axioms Ptx.ScopedExamples.cluster_target_rejected
#print axioms Ptx.ScopedExamples.cluster_target_accepted
#print axioms Ptx.ScopedExamples.local_other_thread_rejected
#print axioms Ptx.ScopedExamples.entry_parameter_store_rejected
#print axioms Ptx.ScopedExamples.parameter_abi_explicitly_unsupported
#print axioms Ptx.ScopedExamples.racy_writes_partial_coherence
#print axioms Ptx.ScopedExamples.racy_program_admitted
#print axioms Ptx.ScopedExamples.racy_not_legacy_valid

-- Scalar
#print axioms Ptx.Scalar.update_same
#print axioms Ptx.Scalar.update_other
#print axioms Ptx.Scalar.addressIndex_ok_iff
#print axioms Ptx.Scalar.runWith_sound
#print axioms Ptx.Scalar.run_sound
#print axioms Ptx.Scalar.runWith_trace_length
#print axioms Ptx.Scalar.run_zero
#print axioms Ptx.Scalar.eval_skipped
#print axioms Ptx.Scalar.shift_left_clamped
#print axioms Ptx.Scalar.shift_right_clamped
#print axioms Ptx.Scalar.run_succ
#print axioms Ptx.Scalar.run_add
#print axioms Ptx.Scalar.eval_memory_safe
#print axioms Ptx.Scalar.eval_memory_length
#print axioms Ptx.Scalar.step_memory_safe
#print axioms Ptx.Scalar.step_memory_length
#print axioms Ptx.Scalar.eval_halted
#print axioms Ptx.Scalar.step_halted
#print axioms Ptx.Scalar.runWith_memory_length
#print axioms Ptx.Scalar.run_memory_length
#print axioms Ptx.Scalar.runWith_trace_safe
#print axioms Ptx.Scalar.run_trace_safe
#print axioms Ptx.Scalar.Runs.exists_run
#print axioms Ptx.Scalar.add_modulo
#print axioms Ptx.Scalar.sub_modulo
#print axioms Ptx.Scalar.mul_low_modulo
#print axioms Ptx.Scalar.add64_modulo
#print axioms Ptx.Scalar.validAddress_bytes
#print axioms Ptx.Scalar.unsupported_not_hidden
#print axioms Ptx.Scalar.shift_boundary_examples
#print axioms Ptx.Scalar.unsigned_wrap_examples

-- ScalarText
#print axioms Ptx.Scalar.Text.decode_encode
#print axioms Ptx.Scalar.Text.bare_load_rejected
#print axioms Ptx.Scalar.Text.uniform_branch_rejected
#print axioms Ptx.Scalar.Text.wrong_destination_rejected
#print axioms Ptx.Scalar.Text.decodeOp_supported
#print axioms Ptx.Scalar.Text.immediate_store_rejected
#print axioms Ptx.Scalar.Text.decode_supported

-- ScalarKernels
#print axioms Ptx.Scalar.Kernels.add_lane_result
#print axioms Ptx.Scalar.Kernels.elementwise_add
#print axioms Ptx.Scalar.Kernels.loop_zero
#print axioms Ptx.Scalar.Kernels.loop_advance
#print axioms Ptx.Scalar.Kernels.sum_loop_correct
#print axioms Ptx.Scalar.Kernels.add_lane_exists
#print axioms Ptx.Scalar.Kernels.sum_loop_exists
#print axioms Ptx.Scalar.Kernels.sum_loop_extra_fuel
#print axioms Ptx.Scalar.Kernels.sum_loop_memory_safe

-- ScalarEnvironment
#print axioms Ptx.Scalar.arena_access_iff
#print axioms Ptx.Scalar.run_environment_safe
#print axioms Ptx.Scalar.separate_arenas
#print axioms Ptx.Scalar.arena_forms_eligible

-- ScalarExamples
#print axioms Ptx.Scalar.Examples.zero_count_no_access
#print axioms Ptx.Scalar.Examples.modular_sum
#print axioms Ptx.Scalar.Examples.fuel_exhaustion_is_not_halt
#print axioms Ptx.Scalar.Examples.misaligned_load_fault
#print axioms Ptx.Scalar.Examples.out_of_bounds_load_fault
#print axioms Ptx.Scalar.Examples.skipped_load_no_fault
#print axioms Ptx.Scalar.Examples.invalid_pc_is_explicit
#print axioms Ptx.Scalar.Examples.unsupported_is_explicit
#print axioms Ptx.Scalar.Examples.add_lane_text_roundtrip
#print axioms Ptx.Scalar.Examples.sum_loop_text_roundtrip

-- ScalarMemoryWitness
#print axioms Ptx.Scalar.MemoryWitness.events_eq
#print axioms Ptx.Scalar.MemoryWitness.graph_event
#print axioms Ptx.Scalar.MemoryWitness.graph_source
#print axioms Ptx.Scalar.MemoryWitness.graph_event0
#print axioms Ptx.Scalar.MemoryWitness.graph_event1
#print axioms Ptx.Scalar.MemoryWitness.graph_event2
#print axioms Ptx.Scalar.MemoryWitness.graph_event3
#print axioms Ptx.Scalar.MemoryWitness.graph_event4
#print axioms Ptx.Scalar.MemoryWitness.graph_event5
#print axioms Ptx.Scalar.MemoryWitness.candidate_result
#print axioms Ptx.Scalar.MemoryWitness.input_sources
#print axioms Ptx.Scalar.MemoryWitness.candidate_correct
#print axioms Ptx.Scalar.MemoryWitness.witness_valid
#print axioms Ptx.Scalar.MemoryWitness.candidate_eq_concrete
#print axioms Ptx.Scalar.MemoryWitness.label_preserves_address
#print axioms Ptx.Scalar.MemoryWitness.witness_events_from_run
#print axioms Ptx.Scalar.MemoryWitness.constructive_execution

/-! Reusable proof rules and shared-allocation vector addition. -/

-- ScalarRules
#print axioms Ptx.Scalar.Rules.segment_comp
#print axioms Ptx.Scalar.Rules.segment_then_completed
#print axioms Ptx.Scalar.Rules.segment_then_total
#print axioms Ptx.Scalar.Rules.completed_total
#print axioms Ptx.Scalar.Rules.eval_frame
#print axioms Ptx.Scalar.Rules.step_frame
#print axioms Ptx.Scalar.Rules.runWith_frame
#print axioms Ptx.Scalar.Rules.run_frame
#print axioms Ptx.Scalar.Rules.runWith_invariant
#print axioms Ptx.Scalar.Rules.partial_of_invariant
#print axioms Ptx.Scalar.Rules.terminates_of_decreasing_measure

-- SharedVector
#print axioms Ptx.Scalar.SharedVector.replace_same
#print axioms Ptx.Scalar.SharedVector.replace_other
#print axioms Ptx.Scalar.SharedVector.initial_invariant
#print axioms Ptx.Scalar.SharedVector.output_ne_left
#print axioms Ptx.Scalar.SharedVector.output_ne_right
#print axioms Ptx.Scalar.SharedVector.output_injective
#print axioms Ptx.Scalar.SharedVector.get_set_other
#print axioms Ptx.Scalar.SharedVector.get_set_same
#print axioms Ptx.Scalar.SharedVector.advance_other
#print axioms Ptx.Scalar.SharedVector.advance_frame
#print axioms Ptx.Scalar.SharedVector.advance_invariant
#print axioms Ptx.Scalar.SharedVector.execute_invariant
#print axioms Ptx.Scalar.SharedVector.execute_frame
#print axioms Ptx.Scalar.SharedVector.completed_correct
#print axioms Ptx.Scalar.SharedVector.pointer_index
#print axioms Ptx.Scalar.SharedVector.advance_is_scalar_step
#print axioms Ptx.Scalar.SharedVector.exit_is_scalar_step
#print axioms Ptx.Scalar.SharedVector.scheduled_access_safe
#print axioms Ptx.Scalar.SharedVector.cursor_advance
#print axioms Ptx.Scalar.SharedVector.execute_cursor
#print axioms Ptx.Scalar.SharedVector.schedule_length
#print axioms Ptx.Scalar.SharedVector.schedule_complete
#print axioms Ptx.Scalar.SharedVector.faithful_step
#print axioms Ptx.Scalar.SharedVector.execute_faithful
#print axioms Ptx.Scalar.SharedVector.completed_execution_exists
#print axioms Ptx.Scalar.SharedVector.emitted_canonical
#print axioms Ptx.Scalar.SharedVector.emitted_thread
#print axioms Ptx.Scalar.SharedVector.filter_emitted
#print axioms Ptx.Scalar.SharedVector.trace_correspondence
#print axioms Ptx.Scalar.SharedVector.completed_trace
#print axioms Ptx.Scalar.SharedVector.emitted_access_safe
#print axioms Ptx.Scalar.SharedVector.trace_access_safe

-- SharedVectorExamples
#print axioms Ptx.Scalar.SharedVector.Examples.round_robin_result
#print axioms Ptx.Scalar.SharedVector.Examples.uneven_result
#print axioms Ptx.Scalar.SharedVector.Examples.unfair_schedule_incomplete
#print axioms Ptx.Scalar.SharedVector.Examples.concrete_execution_exists
#print axioms Ptx.Scalar.SharedVector.Examples.empty_arena_not_faithful
#print axioms Ptx.Scalar.Rules.Examples.set_segment
#print axioms Ptx.Scalar.Rules.Examples.exit_segment
#print axioms Ptx.Scalar.Rules.Examples.composed_completion
#print axioms Ptx.Scalar.Rules.Examples.composed_frame

-- SharedVectorMemory
#print axioms Ptx.Scalar.SharedVectorMemory.lane_index
#print axioms Ptx.Scalar.SharedVectorMemory.slot_index
#print axioms Ptx.Scalar.SharedVectorMemory.index_eta
#print axioms Ptx.Scalar.SharedVectorMemory.index_eq
#print axioms Ptx.Scalar.SharedVectorMemory.forall_index_iff
#print axioms Ptx.Scalar.SharedVectorMemory.exists_index_iff
#print axioms Ptx.Scalar.SharedVectorMemory.event0
#print axioms Ptx.Scalar.SharedVectorMemory.event1
#print axioms Ptx.Scalar.SharedVectorMemory.event2
#print axioms Ptx.Scalar.SharedVectorMemory.event3
#print axioms Ptx.Scalar.SharedVectorMemory.event4
#print axioms Ptx.Scalar.SharedVectorMemory.event5
#print axioms Ptx.Scalar.SharedVectorMemory.graph_event
#print axioms Ptx.Scalar.SharedVectorMemory.witness_valid
#print axioms Ptx.Scalar.SharedVectorMemory.shared_trace_labels
#print axioms Ptx.Scalar.SharedVectorMemory.verified_shared_execution
#print axioms Ptx.Scalar.SharedVectorMemory.initial_labels
#print axioms Ptx.Scalar.SharedVectorMemory.input_writer
#print axioms Ptx.Scalar.SharedVectorMemory.input_sources
#print axioms Ptx.Scalar.SharedVectorMemory.candidate_event_eq
#print axioms Ptx.Scalar.SharedVectorMemory.candidate_shared_trace_labels
#print axioms Ptx.Scalar.SharedVectorMemory.candidate_output

/-! Bytewise observations, atomicity and exact whole-word specialization. -/

-- ByteMemory
#print axioms Ptx.word_eq_of_bytes
#print axioms Ptx.ByteGraph.rf_projection
#print axioms Ptx.ByteGraph.readsWhole_projection
#print axioms Ptx.ByteGraph.observation_projection
#print axioms Ptx.ByteGraph.sync_projection
#print axioms Ptx.ByteGraph.base_projection
#print axioms Ptx.ByteGraph.cause_projection
#print axioms Ptx.ByteGraph.communication_projection
#print axioms Ptx.ByteGraph.location_projection
#print axioms Ptx.ByteGraph.sources_projection
#print axioms Ptx.ByteGraph.coherent_projection
#print axioms Ptx.ByteGraph.projection_valid_iff
#print axioms Ptx.ByteGraph.ofScoped_uniform
#print axioms Ptx.ByteGraph.ofScoped_valid_iff
#print axioms Ptx.ByteGraph.uniform_policy_independent
#print axioms Ptx.ByteGraph.coherence_later_not_initial
#print axioms Ptx.ByteGraph.sources_uniform_at
#print axioms Ptx.ByteGraph.uniform_of_all_in_scope
#print axioms Ptx.ByteGraph.all_in_scope_valid_iff
#print axioms Ptx.Program.byteGraph_access_safe

-- ByteExamples
#print axioms Ptx.ByteExamples.result_eq
#print axioms Ptx.ByteExamples.little_endian_example
#print axioms Ptx.ByteExamples.torn_valid
#print axioms Ptx.ByteExamples.torn_value_is_new
#print axioms Ptx.ByteExamples.torn_execution_exists
#print axioms Ptx.ByteExamples.in_scope_torn_forbidden
#print axioms Ptx.ByteExamples.torn_projection_invalid
#print axioms Ptx.ByteExamples.equal_value_not_uniform
#print axioms Ptx.ByteExamples.memory_safe

#print axioms Ptx.Graph.direct_sync
#print axioms Ptx.Graph.publication_cause
#print axioms Ptx.Graph.source_of_latest
#print axioms Ptx.Graph.value_of_source
#print axioms Ptx.Graph.source_of_initial_or_write
#print axioms Ptx.Scalar.IntegerMinMax.min_toNat
#print axioms Ptx.Scalar.IntegerMinMax.max_toNat
#print axioms Ptx.Scalar.IntegerMinMax.min_mem
#print axioms Ptx.Scalar.IntegerMinMax.max_mem
#print axioms Ptx.Scalar.IntegerMinMax.min_comm
#print axioms Ptx.Scalar.IntegerMinMax.max_comm
#print axioms Ptx.Scalar.IntegerMinMax.min_idem
#print axioms Ptx.Scalar.IntegerMinMax.max_idem
#print axioms Ptx.Scalar.IntegerMinMax.min_bounds
#print axioms Ptx.Scalar.IntegerMinMax.max_bounds
#print axioms Ptx.Scalar.IntegerMinMax.min_exec
#print axioms Ptx.Scalar.IntegerMinMax.max_exec
#print axioms Ptx.Scalar.IntegerMinMax.min_exec_preserves_other
#print axioms Ptx.Scalar.IntegerMinMax.max_exec_preserves_other
#print axioms Ptx.Scalar.IntegerMinMax.min_false
#print axioms Ptx.Scalar.IntegerMinMax.max_false
#print axioms Ptx.Scalar.Ordered.run_sound
#print axioms Ptx.Scalar.Ordered.run_safe
#print axioms Ptx.Scalar.Ordered.skipped_no_label
#print axioms Ptx.Scalar.Ordered.label_origin
#print axioms Ptx.Scalar.Ordered.label_byte_address
#print axioms Ptx.Scalar.Ordered.label_complete
#print axioms Ptx.Scalar.Ordered.events_origin
#print axioms Ptx.Scalar.Ordered.decode_encode
#print axioms Ptx.Scalar.Ordered.literal_store_rejected
#print axioms Ptx.Scalar.ComputedPublication.events_eq
#print axioms Ptx.Scalar.ComputedPublication.graph_event
#print axioms Ptx.Scalar.ComputedPublication.graph_source
#print axioms Ptx.Scalar.ComputedPublication.event0
#print axioms Ptx.Scalar.ComputedPublication.event1
#print axioms Ptx.Scalar.ComputedPublication.event2
#print axioms Ptx.Scalar.ComputedPublication.event3
#print axioms Ptx.Scalar.ComputedPublication.event4
#print axioms Ptx.Scalar.ComputedPublication.event5
#print axioms Ptx.Scalar.ComputedPublication.event6
#print axioms Ptx.Scalar.ComputedPublication.event7
#print axioms Ptx.Scalar.ComputedPublication.event8
#print axioms Ptx.Scalar.ComputedPublication.event9
#print axioms Ptx.Scalar.ComputedPublication.fin_cases
#print axioms Ptx.Scalar.ComputedPublication.input_sources
#print axioms Ptx.Scalar.ComputedPublication.run_results
#print axioms Ptx.Scalar.ComputedPublication.publication
#print axioms Ptx.Scalar.ComputedPublication.publication_observed
#print axioms Ptx.Scalar.ComputedPublication.success_valid
#print axioms Ptx.Scalar.ComputedPublication.stale_valid
#print axioms Ptx.Scalar.ComputedPublication.success_values_grounded
#print axioms Ptx.Scalar.ComputedPublication.stale_values_grounded
#print axioms Ptx.Scalar.ComputedPublication.success_value_acyclic
#print axioms Ptx.Scalar.ComputedPublication.stale_value_acyclic
#print axioms Ptx.Scalar.ComputedPublication.producer_concrete
#print axioms Ptx.Scalar.ComputedPublication.successful_execution
#print axioms Ptx.Scalar.ComputedPublication.relaxed_counterexample
#print axioms Ptx.Scalar.ComputedPublication.producer_safe
#print axioms Ptx.Scalar.ComputedPublication.consumer_safe
#print axioms Ptx.Scalar.ComputedPublication.graph_memory_safe

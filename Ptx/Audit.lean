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

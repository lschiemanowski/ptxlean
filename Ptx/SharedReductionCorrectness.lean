import Ptx.SharedReductionMemoryUniversal
import Ptx.SharedReductionWriteback
import Ptx.SharedReductionSafety

/-! Public entry points keeping result, existence and access safety explicit. -/
namespace Ptx.Scalar.SharedReduction.Correctness
open Machine

/-- A concrete finite fetched execution, its exact final storage and all-thread
completion, and source/coherence choices for its actual combined trace. The
separate grounding conclusion is sufficient for this witness, not a general
restriction on other PTX executions. -/
theorem completed_execution (cfg : Config n) (input scratch : List Word) (seeds : Fin n → Seed)
    (inputs : n < input.length) (storage : n ≤ scratch.length) :
    let execution := Machine.run cfg (fullSchedule cfg) (start input scratch seeds)
    Machine.Runs cfg (start input scratch seeds) (fullSchedule cfg) execution ∧
    execution.state.global = input.set n (total input n) ∧
    execution.state.shared = input.take n ++ scratch.drop n ∧
    execution.state.barrier = Barrier.reset 1 ∧
    (∀ thread, (execution.state.lanes thread).halted = true) ∧
    ∃ source co,
      let g := Memory.graph input scratch execution.trace source co
      let order := Memory.extra input scratch execution.trace source co
      Graph.Ordered.Valid g order ∧ ∀ event, ¬Path (Memory.grounding g order) event event := by
  have result := full_execution cfg input scratch seeds inputs storage
  exact ⟨Machine.run_sound cfg _ _,result.1,result.2.1,result.2.2.1,result.2.2.2,
    Memory.canonical_valid_exists cfg input scratch seeds inputs storage⟩

/-- Safety concerns every emitted access under any finite schedule/read choices;
no completion or memory-admission assumption is required. -/
theorem emitted_access_safe (cfg : Config n) (reads : Nat → Option Word) (schedule : List (Fin n))
    (input scratch : List Word) (seeds : Fin n → Seed)
    (thread : Fin n) (block : Machine.Block) (space : Space) (event : Occurrence) (effect : MemoryEffect)
    (member : .scalar thread block (some space) event ∈
      (Machine.runWith cfg reads schedule (start input scratch seeds)).trace)
    (memory : event.memory = some effect) :
    Scalar.ValidAddress (match space with | .global => input | .shared => scratch) effect.address := by
  cases space <;> exact Safety.run_memory_safe cfg reads schedule (start input scratch seeds)
    thread block _ event effect member memory

/-- Actual execution and memory constraints discharge the arithmetic layer's
read contract. The caller does not supply fresh values or source identities. -/
theorem read_contract (cfg : Config n) (reads : Nat → Option Word) (schedule : List (Fin n))
    (input scratch : List Word) (seeds : Fin n → Seed) (source co)
    (valid : Graph.Ordered.Valid
      (Memory.runGraph cfg reads schedule (start input scratch seeds) source co)
      (Memory.extra input scratch (Machine.runWith cfg reads schedule (start input scratch seeds)).trace source co)) :
    ResultProof.ReadContract n input (Machine.runWith cfg reads schedule (start input scratch seeds)).trace := by
  intro thread block event effect index member memory load inside address
  exact Memory.run_shared_load_member_value cfg reads schedule input scratch seeds
    thread block event effect member memory load index inside address source co valid

/-- Under the actual combined memory constraints, every emitted global store
writes the complete modular sum to the separate output slot. This ranges over
all finite schedules and candidate read choices, not just the constructed witness.
The storage-length premise describes the supplied input, not the desired result. -/
theorem candidate_output (cfg : Config n) (reads : Nat → Option Word) (schedule : List (Fin n))
    (input scratch : List Word) (seeds : Fin n → Seed) (extent : n ≤ input.length) (source co)
    (valid : Graph.Ordered.Valid
      (Memory.runGraph cfg reads schedule (start input scratch seeds) source co)
      (Memory.extra input scratch (Machine.runWith cfg reads schedule (start input scratch seeds)).trace source co))
    (thread : Fin n) (block : Machine.Block) (event : Occurrence) (effect : MemoryEffect)
    (member : .scalar thread block (some .global) event ∈
      (Machine.runWith cfg reads schedule (start input scratch seeds)).trace)
    (memory : event.memory = some effect) (store : effect.kind = .store) :
    effect.address = bytePointer n ∧ effect.value = total input n := by
  exact ⟨Control.runWith_global_store_address cfg reads schedule _ thread block event effect member memory store,
    ResultProof.global_store_sum cfg reads schedule input scratch seeds extent
      (read_contract cfg reads schedule input scratch seeds source co valid)
      thread block event effect member memory store⟩

/-- If the actual leader has exited, admitted candidate execution has written
exactly the modular sum, preserving every other global word. This is conditional
correctness for any schedule; finite existence is proved separately above. -/
theorem completed_candidate (cfg : Config n) (reads : Nat → Option Word) (schedule : List (Fin n))
    (input scratch : List Word) (seeds : Fin n → Seed) (extent : n < input.length) (source co)
    (valid : Graph.Ordered.Valid
      (Memory.runGraph cfg reads schedule (start input scratch seeds) source co)
      (Memory.extra input scratch (Machine.runWith cfg reads schedule (start input scratch seeds)).trace source co))
    (leader : Fin n) (zero : leader.val = 0)
    (halted : ((Machine.runWith cfg reads schedule (start input scratch seeds)).state.lanes leader).halted = true) :
    (Machine.runWith cfg reads schedule (start input scratch seeds)).state.global = input.set n (total input n) :=
  Writeback.halted_leader cfg reads schedule input scratch seeds extent
    (read_contract cfg reads schedule input scratch seeds source co valid) leader zero halted

end Ptx.Scalar.SharedReduction.Correctness

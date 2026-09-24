import Ptx.ScalarKernels
import Ptx.ScalarEnvironment
import Ptx.Barrier

/-! Actual local blocks for a staged integer reduction. The producer's arena is
explicit global storage; the leader's load arena is explicitly shared storage.
Connecting all blocks to one fetched concurrent program and candidate graph is a
separate obligation. No assembled-kernel correctness claim is made here. -/
namespace Ptx.Scalar.SharedReduction

structure Config (n : Nat) where
  nonempty : 0 < n
  noWrap : 4*n < 2^32
  cta : Nat

structure Seed where
  registers : Nat → Word
  addresses : Nat → Address
  predicates : Nat → Bool

/-- Supplied lane identity is converted and multiplied by four by real instructions. -/
def producerProgram : List Instr := [
  .plain (.cvt64 0 (.reg 0)),
  .plain (.add64 0 (.reg 0) (.reg 0)),
  .plain (.add64 0 (.reg 0) (.reg 0)),
  .plain (.load 1 (.reg 0))]

def producerStart (input : List Word) (lane : Fin n) (seed : Seed) : State :=
  ⟨0, update seed.registers 0 (BitVec.ofNat 32 lane.val), seed.addresses,
    seed.predicates, input⟩

def producer (input : List Word) (lane : Fin n) (seed : Seed) : RunResult :=
  run 4 producerProgram (producerStart input lane seed)

def bytePointer (index : Nat) : Address := BitVec.ofNat 64 (4*index)

/-- The global-load prefix remains a prefix: it has not exited or crossed a barrier. -/
theorem producer_correct (cfg : Config n) (input : List Word) (lane : Fin n) (seed : Seed)
    (extent : n ≤ input.length) :
    (producer input lane seed).status = .exhausted ∧
    (producer input lane seed).state.pc = 4 ∧
    (producer input lane seed).state.memory = input ∧
    (producer input lane seed).state.regs 1 = input[lane.val]! ∧
    (producer input lane seed).state.addrs 0 = bytePointer lane.val := by
  have laneFits : lane.val < 2^32 := by have := cfg.noWrap; have := lane.isLt; omega
  have pointerFits : 4*lane.val < 2^64 := by have := cfg.noWrap; have := lane.isLt; omega
  have double : (BitVec.ofNat 64 lane.val + BitVec.ofNat 64 lane.val : Address) =
      BitVec.ofNat 64 (2*lane.val) := by rw [← BitVec.ofNat_add]; congr 1; omega
  have four : (BitVec.ofNat 64 (2*lane.val) + BitVec.ofNat 64 (2*lane.val) : Address) =
      bytePointer lane.val := by rw [← BitVec.ofNat_add]; simp [bytePointer]; congr 1; omega
  have index : addressIndex input (bytePointer lane.val) = .ok lane.val := by
    simp [addressIndex, bytePointer, Nat.mod_eq_of_lt pointerFits, show lane.val < input.length by omega]
  simp [producer, run, runWith, stepWith, producerProgram, producerStart,
    Instr.plain, eval, Guard.eval, Operand32.eval, Operand64.eval, update,
    Nat.mod_eq_of_lt laneFits, double, four, index]

/-- A shared-store block consumes the actual producer registers and computed address.
Its arena argument changes state space explicitly; this is not a global store label. -/
def sharedStore : Instr := .plain (.store (.reg 0) (.reg 1))

def publicationStart (input scratch : List Word) (lane : Fin n) (seed : Seed) : State :=
  {(producer input lane seed).state with memory := scratch}

def publication (input scratch : List Word) (lane : Fin n) (seed : Seed) : StepResult :=
  eval none sharedStore (publicationStart input scratch lane seed)

theorem publication_correct (cfg : Config n) (input scratch : List Word)
    (lane : Fin n) (seed : Seed) (inputs : n ≤ input.length) (storage : n ≤ scratch.length) :
    ∃ next event,
      publication input scratch lane seed = .next next event ∧
      next.pc = 5 ∧ next.memory = scratch.set lane.val input[lane.val]! ∧
      event.pc = 4 ∧ event.instruction = sharedStore ∧
      event.memory = some ⟨.store, bytePointer lane.val, input[lane.val]!⟩ := by
  obtain ⟨_, pc, _, value, pointer⟩ := producer_correct cfg input lane seed inputs
  have fits : 4*lane.val < 2^64 := by have := cfg.noWrap; have := lane.isLt; omega
  have index : addressIndex scratch (bytePointer lane.val) = .ok lane.val := by
    simp [addressIndex, bytePointer, Nat.mod_eq_of_lt fits, show lane.val < scratch.length by omega]
  simp [publication, publicationStart, sharedStore, Instr.plain, eval, Guard.eval,
    Operand32.eval, Operand64.eval, pointer, value, index, occurrence, pc]
  exact ⟨_, _, ⟨rfl, rfl⟩, rfl, rfl, rfl, rfl, rfl⟩

/-- The load-and-add loop is reused as a shared-arena block. Its memory
form is supplied by the explicit shared block tag below. -/
def leaderProgram : List Instr := Kernels.sumLoop

def leaderStart (n : Nat) (scratch : List Word) (seed : Seed) : State :=
  ⟨0, update (update seed.registers 0 (BitVec.ofNat 32 n)) 1 0,
    update seed.addresses 0 0, seed.predicates, scratch⟩

def leader (n : Nat) (scratch : List Word) (seed : Seed) : RunResult :=
  run (7*n+3) leaderProgram (leaderStart n scratch seed)

def total (input : List Word) (n : Nat) : Word :=
  (input.take n).foldl (fun sum value => sum+value) 0

theorem leader_correct (cfg : Config n) (scratch : List Word) (seed : Seed)
    (extent : n ≤ scratch.length) :
    (leader n scratch seed).status = .halted ∧
    (leader n scratch seed).state.memory = scratch ∧
    (leader n scratch seed).state.regs 1 = total scratch n := by
  have countFits : n < 2^32 := by have := cfg.noWrap; omega
  have addressFits : 4*n < 2^64 := by have := cfg.noWrap; omega
  simpa [leader, leaderProgram, leaderStart, Kernels.outcome, Kernels.sliceSum, total, update] using
    Kernels.sum_loop_correct n (leaderStart n scratch seed) 0 rfl
      (by simp [leaderStart,update]) (by simp [leaderStart,update]) (by simpa [leaderStart] using extent)
      countFits (by simpa using addressFits)

theorem leader_execution (n : Nat) (scratch : List Word) (seed : Seed) :
    Runs leaderProgram (fun _ => none) (leaderStart n scratch seed) (leader n scratch seed) :=
  run_sound _ _ _

theorem leader_safe (n : Nat) (scratch : List Word) (seed : Seed)
    (event : Occurrence) (member : event ∈ (leader n scratch seed).trace)
    (effect : MemoryEffect) (memory : event.memory = some effect) :
    ValidAddress scratch effect.address :=
  run_trace_safe _ _ _ event member effect memory

/-- Actual producer accesses are checked against the original global arena. -/
theorem producer_safe (input : List Word) (lane : Fin n) (seed : Seed)
    (event : Occurrence) (member : event ∈ (producer input lane seed).trace)
    (effect : MemoryEffect) (memory : event.memory = some effect) :
    ValidAddress input effect.address := run_trace_safe _ _ _ event member effect memory

/-- A barrier request uses the actual producer+publication continuation PC5.
There is one immediate resource0, full participation, and no pre-barrier exit. -/
def barrierConfig (cfg : Config n) : Barrier.Config n :=
  ⟨cfg.cta, 0, 5, cfg.nonempty⟩

theorem barrier_round_exists (cfg : Config n) :
    ∃ requests : List (Barrier.Request n), requests.length = n ∧
      Barrier.Runs (barrierConfig cfg) (Barrier.reset 0) requests (Barrier.reset 1) :=
  Barrier.round_exists (barrierConfig cfg) 0



/-- Space and scope belong to the typed block, never inferred from its numeric addresses. -/
inductive Space where
  | global | shared
  deriving DecidableEq, Repr

structure Block where
  space : Space
  code : List Instr

def Block.scope (block : Block) : Scope :=
  match block.space with | .global => .gpu | .shared => .cta

/-- Scalar instructions specify local register evaluation. Memory forms are the
explicit relaxed/u32 form in this block's space and scope. -/
def Block.memoryForm (block : Block) (kind : MemoryKind) : String :=
  match block.space, kind with
  | .global, .load => "ld.relaxed.gpu.global.u32"
  | .global, .store => "st.relaxed.gpu.global.u32"
  | .shared, .load => "ld.relaxed.cta.shared.u32"
  | .shared, .store => "st.relaxed.cta.shared.u32"

def producerBlock : Block := ⟨.global, producerProgram⟩
def publicationBlock : Block := ⟨.shared, [sharedStore]⟩
def leaderBlock : Block := ⟨.shared, leaderProgram⟩

/-- Different spaces remain different even when their byte offsets coincide. -/
def Block.project (block : Block) (event : Occurrence) : Option (Space × Scope × MemoryEffect) :=
  event.memory.map (fun effect => (block.space, block.scope, effect))

theorem project_origin (block : Block) (event : Occurrence) (space scope effect)
    (emitted : block.project event = some (space, scope, effect)) :
    space = block.space ∧ scope = block.scope ∧ event.memory = some effect := by
  cases h : event.memory with
  | none => simp [Block.project, h] at emitted
  | some original =>
    simp [Block.project, h] at emitted
    obtain ⟨rfl, rfl, rfl⟩ := emitted
    exact ⟨rfl, rfl, rfl⟩

theorem project_complete (block : Block) (event : Occurrence) (effect : MemoryEffect)
    (emitted : event.memory = some effect) :
    block.project event = some (block.space, block.scope, effect) := by
  simp [Block.project, emitted]

/-- Determinism of concrete local execution, including its entire dynamic trace. -/
theorem halted_unique (program : List Instr) (s : State) (first second : Nat)
    (a : (run first program s).status = .halted)
    (b : (run second program s).status = .halted) :
    run first program s = run second program s := by
  have left := run_add first second program s
  have right := run_add second first program s
  simp only [resume, a, b, reduceCtorEq, ↓reduceIte] at left right
  rw [Nat.add_comm] at right
  exact left.symm.trans right

/-- Every completed concrete leader run has the same result and trace, whatever
sufficient fuel was supplied. No desired output premise occurs here. -/
theorem leader_any_completed (cfg : Config n) (scratch : List Word) (seed : Seed)
    (extent : n ≤ scratch.length) (fuel : Nat)
    (done : (run fuel leaderProgram (leaderStart n scratch seed)).status = .halted) :
    run fuel leaderProgram (leaderStart n scratch seed) = leader n scratch seed :=
  halted_unique _ _ fuel (7*n+3) done (leader_correct cfg scratch seed extent).1

/-- The publication transition itself supplies the new memory; no expected value
is installed by this executable fold. Failed transitions retain their old arena,
and the correctness proof separately rules out those failures on valid inputs. -/
def publishAll (input : List Word) (seeds : Fin n → Seed) :
    List (Fin n) → List Word → List Word
  | [], scratch => scratch
  | lane :: rest, scratch =>
      match publication input scratch lane (seeds lane) with
      | .next next _ => publishAll input seeds rest next.memory
      | _ => scratch

theorem publishAll_cons (cfg : Config n) (input scratch : List Word)
    (seeds : Fin n → Seed) (lane : Fin n) (rest : List (Fin n))
    (inputs : n ≤ input.length) (storage : n ≤ scratch.length) :
    publishAll input seeds (lane :: rest) scratch =
      publishAll input seeds rest (scratch.set lane.val input[lane.val]!) := by
  obtain ⟨next, event, executed, _, memory, _⟩ := publication_correct cfg input scratch lane (seeds lane) inputs storage
  simp [publishAll, executed, memory]

theorem publishAll_length (cfg : Config n) (input scratch : List Word)
    (seeds : Fin n → Seed) (lanes : List (Fin n))
    (inputs : n ≤ input.length) (storage : n ≤ scratch.length) :
    (publishAll input seeds lanes scratch).length = scratch.length := by
  induction lanes generalizing scratch with
  | nil => rfl
  | cons lane rest ih =>
    rw [publishAll_cons cfg input scratch seeds lane rest inputs storage]
    simpa using ih (scratch.set lane.val input[lane.val]!) (by simpa using storage)

/-- Every visited slot contains its actual global input; unvisited slots retain
initial scratch. This also proves order/duplicate independence of publication. -/
theorem publishAll_lookup (cfg : Config n) (input scratch : List Word)
    (seeds : Fin n → Seed) (lanes : List (Fin n))
    (inputs : n ≤ input.length) (storage : n ≤ scratch.length) (index : Nat) :
    (publishAll input seeds lanes scratch)[index]? =
      if ∃ lane ∈ lanes, lane.val = index then input[index]? else scratch[index]? := by
  induction lanes generalizing scratch with
  | nil => simp [publishAll]
  | cons lane rest ih =>
    rw [publishAll_cons cfg input scratch seeds lane rest inputs storage]
    rw [ih _ (by simpa using storage)]
    by_cases visited : ∃ other ∈ rest, other.val = index
    · simp [visited]
    · by_cases same : lane.val = index
      · subst index
        have si : lane.val < scratch.length := by have := lane.isLt; omega
        have ii : lane.val < input.length := by have := lane.isLt; omega
        simp [visited, si, ii]
      · simp [visited, same, List.getElem?_set_ne same]

/-- A full finite enumeration copies only the prefix, from actual producer/store steps. -/
theorem publication_all (cfg : Config n) (input scratch : List Word)
    (seeds : Fin n → Seed) (inputs : n ≤ input.length) (storage : n ≤ scratch.length) :
    publishAll input seeds (List.finRange n) scratch = input.take n ++ scratch.drop n := by
  apply List.ext_getElem?
  intro index
  rw [publishAll_lookup cfg input scratch seeds (List.finRange n) inputs storage]
  have visits : (∃ lane ∈ List.finRange n, lane.val = index) ↔ index < n := by
    constructor
    · rintro ⟨lane, _, rfl⟩; exact lane.isLt
    · intro h; exact ⟨⟨index,h⟩, List.mem_finRange _, rfl⟩
  simp only [visits]
  by_cases inside : index < n
  · simp [inside, List.getElem?_append, List.length_take, Nat.min_eq_left inputs]
  · simp [inside, List.getElem?_append, List.length_take, Nat.min_eq_left inputs, Nat.add_sub_of_le (by omega : n ≤ index)]



/-- The output store reads the actual loop's accumulator register. -/
def outputProgram : List Instr := [.plain (.store (.imm 0) (.reg 1)), .plain .exit]

def outputStart (loopFinal : State) (old : Word) (tail : List Word) : State :=
  {loopFinal with pc := 0, memory := old :: tail}

def output (loopFinal : State) (old : Word) (tail : List Word) : RunResult :=
  run 2 outputProgram (outputStart loopFinal old tail)

def outputBlock : Block := ⟨.global, outputProgram⟩

theorem output_correct (loopFinal : State) (old : Word) (tail : List Word) :
    (output loopFinal old tail).status = .halted ∧
    (output loopFinal old tail).state.memory = loopFinal.regs 1 :: tail ∧
    (output loopFinal old tail).trace.length = 2 := by
  simp [output, outputProgram, outputStart, run, runWith, stepWith, eval, Instr.plain,
    Guard.eval, Operand64.eval, Operand32.eval, addressIndex, occurrence]

theorem output_execution (loopFinal : State) (old : Word) (tail : List Word) :
    Runs outputProgram (fun _ => none) (outputStart loopFinal old tail) (output loopFinal old tail) :=
  run_sound _ _ _

theorem output_safe (loopFinal : State) (old : Word) (tail : List Word)
    (event : Occurrence) (member : event ∈ (output loopFinal old tail).trace)
    (effect : MemoryEffect) (memory : event.memory = some effect) :
    ValidAddress (old :: tail) effect.address := run_trace_safe _ _ _ event member effect memory

/-- Reference total of a published prefix does not depend on scratch's old tail. -/
theorem total_publication (cfg : Config n) (input scratch : List Word)
    (seeds : Fin n → Seed) (inputs : n ≤ input.length) (storage : n ≤ scratch.length) :
    total (publishAll input seeds (List.finRange n) scratch) n = total input n := by
  rw [publication_all cfg input scratch seeds inputs storage]
  simp [total, List.length_take, Nat.min_eq_left inputs]

/-- The constructive staged result. Its producer and store blocks, barrier control
run, leader loop and output store are actual existing execution definitions.
The explicit block-entry rebinding is not claimed to be a fetched concurrent kernel. -/
theorem staged_execution (cfg : Config n) (input scratch : List Word)
    (seeds : Fin n → Seed) (leaderSeed : Seed) (old : Word) (tail : List Word)
    (inputs : n ≤ input.length) (storage : n ≤ scratch.length) :
    let published := publishAll input seeds (List.finRange n) scratch
    let loop := leader n published leaderSeed
    let stored := output loop.state old tail
    (∀ lane, (producer input lane (seeds lane)).status = .exhausted ∧
      (producer input lane (seeds lane)).state.regs 1 = input[lane.val]!) ∧
    published = input.take n ++ scratch.drop n ∧
    (∃ requests : List (Barrier.Request n), requests.length = n ∧
      Barrier.Runs (barrierConfig cfg) (Barrier.reset 0) requests (Barrier.reset 1)) ∧
    Runs leaderProgram (fun _ => none) (leaderStart n published leaderSeed) loop ∧
    loop.status = .halted ∧ loop.state.memory = published ∧
    Runs outputProgram (fun _ => none) (outputStart loop.state old tail) stored ∧
    stored.status = .halted ∧ stored.state.memory = total input n :: tail := by
  dsimp only
  have extent : n ≤ (publishAll input seeds (List.finRange n) scratch).length := by
    rw [publishAll_length cfg input scratch seeds (List.finRange n) inputs storage]
    exact storage
  have loop := leader_correct cfg (publishAll input seeds (List.finRange n) scratch) leaderSeed extent
  have result := output_correct (leader n (publishAll input seeds (List.finRange n) scratch) leaderSeed).state old tail
  refine ⟨?_, publication_all cfg input scratch seeds inputs storage, barrier_round_exists cfg,
    leader_execution _ _ _, loop.1, loop.2.1, output_execution _ _ _, result.1, ?_⟩
  · intro lane
    have h := producer_correct cfg input lane (seeds lane) inputs
    exact ⟨h.1, h.2.2.2.1⟩
  · rw [result.2.1, loop.2.2, total_publication cfg input scratch seeds inputs storage]

/-- Instantiations retain real full-CTA participation; geometry remains external. -/
def oneWarp (cta : Nat) : Config 32 := ⟨by decide, by decide, cta⟩
def twoWarps (cta : Nat) : Config 64 := ⟨by decide, by decide, cta⟩



/-- Original global producer derivations remain available, including their traces. -/
theorem producer_execution (input : List Word) (lane : Fin n) (seed : Seed) :
    Runs producerProgram (fun _ => none) (producerStart input lane seed) (producer input lane seed) :=
  run_sound _ _ _

/-- A shared block's checked accesses use a CTA-owned allocation contract. -/
def sharedEnvironment (scratch : List Word) (thread : ThreadLocation) (allocation : Nat) : Environment where
  allocations := fun id => if id = allocation then some {
    space := .shared
    bytes := 4*scratch.length
    alignment := 4
    owner := .cta thread
    readable := true
    writable := true
    initialized := true
  } else none

def sharedAddress (allocation : Nat) (pointer : Address) : Ptx.Address :=
  ⟨.shared, allocation, pointer.toNat⟩

theorem shared_access_iff (scratch : List Word) (thread : ThreadLocation)
    (allocation : Nat) (pointer : Address) (kind : AccessKind) :
    (sharedEnvironment scratch thread allocation).accessible thread kind
      (sharedAddress allocation pointer) 4 ↔ ValidAddress scratch pointer := by
  have division := Nat.mod_add_div pointer.toNat 4
  cases kind <;>
    simp [Environment.accessible, Environment.checkAccess, sharedEnvironment,
      sharedAddress, Allocation.ownerAllows, ThreadLocation.sameCTA,
      ThreadLocation.sameCluster, ValidAddress] <;>
    (repeat' split) <;> simp_all <;> omega

theorem leader_environment_safe (n : Nat) (scratch : List Word) (seed : Seed)
    (thread : ThreadLocation) (allocation : Nat)
    (event : Occurrence) (member : event ∈ (leader n scratch seed).trace)
    (effect : MemoryEffect) (memory : event.memory = some effect) :
    (sharedEnvironment scratch thread allocation).accessible thread
      (match effect.kind with | .load => .read | .store => .write)
      (sharedAddress allocation effect.address) 4 :=
  (shared_access_iff ..).mpr (leader_safe _ _ _ event member effect memory)

end Ptx.Scalar.SharedReduction

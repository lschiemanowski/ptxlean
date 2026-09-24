import Ptx.SharedReduction

/-! A fetched block-labelled whole-program machine for the reduction.
Block-qualified labels are ordinary branch destinations. Every change of block,
except a completed barrier's continuation, is a fetched branch instruction.
The scratch view in Scalar.State.memory is internal evaluator bookkeeping; the
shared and global arenas below are the authoritative persistent memory. -/
namespace Ptx.Scalar.SharedReduction.Machine

inductive Block where
  | producer | publish | barrier | choose | initialize | loop | output
  deriving DecidableEq, Repr

structure Label where
  block : Block
  pc : Nat
  deriving DecidableEq, Repr

inductive Instruction where
  | localStep (instruction : Instr)
  | memory (space : Space) (instruction : Instr)
  | branch (guard : Guard) (destination : Label)
  | sync (resource : Fin 16)
  | exit
  deriving DecidableEq, Repr

/-- One fixed source program, with an explicit counter immediate for its CTA size. -/
def program (n : Nat) : Block → List Instruction
  | .producer => [
    .localStep (.plain (.cvt64 0 (.reg 0))),
    .localStep (.plain (.add64 0 (.reg 0) (.reg 0))),
    .localStep (.plain (.add64 0 (.reg 0) (.reg 0))),
    .memory .global (.plain (.load 1 (.reg 0))),
    .branch .always ⟨.publish, 0⟩]
  | .publish => [.memory .shared sharedStore, .branch .always ⟨.barrier,0⟩]
  | .barrier => [.sync 0]
  | .choose => [
    .localStep (.plain (.setp .eq 0 (.reg 0) (.imm 0))),
    .branch (.pred 0 true) ⟨.initialize,0⟩, .exit]
  | .initialize => [
    .localStep (.plain (.mov32 0 (.imm (BitVec.ofNat 32 n)))),
    .localStep (.plain (.mov32 1 (.imm 0))),
    .localStep (.plain (.mov64 0 (.imm 0))),
    .branch .always ⟨.loop,0⟩]
  | .loop => [
    .localStep (.plain (.setp .eq 0 (.reg 0) (.imm 0))),
    .localStep ⟨.pred 0 true, .bra 7⟩,
    .memory .shared (.plain (.load 2 (.reg 0))),
    .localStep (.plain (.bin32 .add 1 (.reg 1) (.reg 2))),
    .localStep (.plain (.add64 0 (.reg 0) (.imm 4))),
    .localStep (.plain (.bin32 .sub 0 (.reg 0) (.imm 1))),
    .localStep (.plain (.bra 0)),
    .branch .always ⟨.output,0⟩]
  | .output => [
    .memory .global (.plain (.store (.imm (bytePointer n)) (.reg 1))), .exit]

structure Lane where
  block : Block
  scalar : Scalar.State
  halted : Bool

structure State (n : Nat) where
  lanes : Fin n → Lane
  global : List Word
  shared : List Word
  barrier : Barrier.State n

inductive Event (n : Nat) where
  | scalar (thread : Fin n) (block : Block) (space : Option Space) (event : Occurrence)
  | branch (thread : Fin n) (origin destination : Label) (taken : Bool)
  | barrier (event : Barrier.Event n)
  | exit (thread : Fin n) (origin : Label)
  deriving DecidableEq, Repr

inductive Status where
  | advanced | waiting | released | halted | invalidPC | rejectedBarrier
  | fault (reason : Fault) | unsupported (name : String)
  deriving DecidableEq, Repr

structure Result (n : Nat) where
  state : State n
  status : Status
  events : List (Event n)

def setLane (s : State n) (thread : Fin n) (lane : Lane) : State n :=
  {s with lanes := fun other => if other = thread then lane else s.lanes other}

def barrierConfig (cfg : Config n) : Barrier.Config n := ⟨cfg.cta, 0, 5, cfg.nonempty⟩

/-- The barrier site is the unique block label, assigned source-site identity5.
The current generation and fetched resource supply the remaining request key. -/
def barrierRequest (cfg : Config n) (s : State n) (thread : Fin n) (resource : Fin 16) : Barrier.Request n :=
  ⟨⟨cfg.cta,resource,s.barrier.generation,5⟩,thread⟩

/-- Reuse Scalar.eval on the actual selected arena. No register or predicate is
reset when switching arenas, and every persistent write is its returned memory. -/
def scalarStep (override : Option Word) (thread : Fin n) (space : Option Space)
    (instruction : Instr) (s : State n) : Result n :=
  let lane := s.lanes thread
  let arena := match space with | some .global => s.global | some .shared => s.shared | none => s.shared
  let input := {lane.scalar with memory := arena}
  match eval override instruction input with
  | .next next event =>
    let installed :=  setLane s thread {lane with scalar := next}
    let final := match space with
      | some .global => {installed with global := next.memory}
      | some .shared => {installed with shared := next.memory}
      | none => installed
    ⟨final, .advanced, [.scalar thread lane.block space event]⟩
  | .halted next event =>
    ⟨setLane s thread {lane with scalar := next, halted := true}, .halted,
      [.scalar thread lane.block space event]⟩
  | .fault reason => ⟨s,.fault reason,[]⟩
  | .unsupported name => ⟨s,.unsupported name,[]⟩

/-- Only fetched instructions reach this dispatcher through step below. -/
def dispatch (cfg : Config n) (override : Option Word) (thread : Fin n)
    (instruction : Instruction) (s : State n) : Result n :=
  let lane := s.lanes thread
  match instruction with
  | .localStep instruction => scalarStep override thread none instruction s
  | .memory space instruction => scalarStep override thread (some space) instruction s
  | .branch guard destination =>
    let taken := guard.eval lane.scalar
    let next := if taken then {lane with block := destination.block, scalar := {lane.scalar with pc := destination.pc}}
      else {lane with scalar := {lane.scalar with pc := lane.scalar.pc+1}}
    ⟨setLane s thread next, .advanced,
      [.branch thread ⟨lane.block,lane.scalar.pc⟩ destination taken]⟩
  | .sync resource =>
    let result := Barrier.step (barrierConfig cfg) s.barrier (barrierRequest cfg s thread resource)
    match result.disposition with
    | .rejectedWrongKey => ⟨s,.rejectedBarrier,[]⟩
    | .waiting => ⟨{s with barrier := result.state}, .waiting, result.events.map Event.barrier⟩
    | .released =>
      ⟨{s with barrier := result.state, lanes := fun other =>
        {s.lanes other with block := .choose, scalar := {(s.lanes other).scalar with pc := 0}}},
        .released, result.events.map Event.barrier⟩
  | .exit =>
    ⟨setLane s thread {lane with halted := true}, .halted, [.exit thread ⟨lane.block,lane.scalar.pc⟩]⟩

def step (cfg : Config n) (override : Option Word) (thread : Fin n) (s : State n) : Result n :=
  let lane := s.lanes thread
  if lane.halted then ⟨s,.halted,[]⟩ else
  match (program n lane.block)[lane.scalar.pc]? with
  | none => ⟨s,.invalidPC,[]⟩
  | some instruction => dispatch cfg override thread instruction s

structure Execution (n : Nat) where
  state : State n
  trace : List (Event n)

def runWith (cfg : Config n) : (Nat → Option Word) → List (Fin n) → State n → Execution n
  | _, [], state => ⟨state,[]⟩
  | reads, thread::rest, state =>
    let first := step cfg (reads 0) thread state
    let next := runWith cfg (fun i => reads (i+1)) rest first.state
    ⟨next.state, first.events ++ next.trace⟩

def run (cfg : Config n) (schedule : List (Fin n)) (state : State n) : Execution n :=
  runWith cfg (fun _ => none) schedule state

def start (input scratch : List Word) (seeds : Fin n → Seed) : State n :=
  ⟨fun lane => ⟨.producer, producerStart input lane (seeds lane), false⟩,
    input, scratch, Barrier.initial⟩

/-- Every run is an actual finite sequence of fetched steps, not a final-state relation. -/
inductive Runs (cfg : Config n) : State n → List (Fin n) → Execution n → Prop where
  | nil : Runs cfg state [] ⟨state,[]⟩
  | cons : Runs cfg (step cfg none thread state).state rest next →
      Runs cfg state (thread::rest) ⟨next.state,(step cfg none thread state).events ++ next.trace⟩

theorem run_sound (cfg : Config n) (schedule : List (Fin n)) (state : State n) :
    Runs cfg state schedule (run cfg schedule state) := by
  induction schedule generalizing state with
  | nil => exact .nil
  | cons thread rest ih => exact .cons (ih _)

theorem step_origin (cfg : Config n) (reads : Option Word) (thread : Fin n) (s : State n)
    (live : (s.lanes thread).halted = false)
    (valid : ∃ instruction, (program n (s.lanes thread).block)[(s.lanes thread).scalar.pc]? = some instruction) :
    ∃ instruction, (program n (s.lanes thread).block)[(s.lanes thread).scalar.pc]? = some instruction ∧
      step cfg reads thread s = dispatch cfg reads thread instruction s := by
  obtain ⟨instruction, fetch⟩ := valid
  exact ⟨instruction, fetch, by simp [step, live, fetch]⟩



@[simp] theorem setLane_same (s : State n) (thread : Fin n) (lane : Lane) :
    (setLane s thread lane).lanes thread = lane := by simp [setLane]
@[simp] theorem setLane_other (s : State n) (thread other : Fin n) (lane : Lane)
    (different : other ≠ thread) : (setLane s thread lane).lanes other = s.lanes other := by
  simp [setLane,different]

theorem run_append (cfg : Config n) (first second : List (Fin n)) (s : State n) :
    run cfg (first ++ second) s =
      let initialPart := run cfg first s
      let suffix := run cfg second initialPart.state
      ⟨suffix.state, initialPart.trace ++ suffix.trace⟩ := by
  induction first generalizing s with
  | nil => simp [run,runWith]
  | cons thread rest ih =>
    have h := ih (step cfg none thread s).state
    simp only [run] at h
    simp only [List.cons_append, run, runWith]
    rw [h]
    simp [List.append_assoc]

/-- A complete actual producer block, including its two fetched cross-block
branches, reaches the common barrier after storing its loaded global word. -/
theorem producer_phase (cfg : Config n) (s : State n) (thread : Fin n) (seed : Seed)
    (entry : s.lanes thread = ⟨.producer, producerStart s.global thread seed, false⟩)
    (inputs : n ≤ s.global.length) (storage : n ≤ s.shared.length) :
    let final := (run cfg (List.replicate 7 thread) s).state
    final.global = s.global ∧ final.shared = s.shared.set thread.val s.global[thread.val]! ∧
    (final.lanes thread).block = .barrier ∧ (final.lanes thread).scalar.pc = 0 ∧
    (final.lanes thread).scalar.regs 0 = BitVec.ofNat 32 thread.val ∧
    (final.lanes thread).halted = false ∧ final.barrier = s.barrier ∧
    (∀ other, other ≠ thread → final.lanes other = s.lanes other) := by
  have fits : thread.val < 2^32 := by have := cfg.noWrap; have := thread.isLt; omega
  have pfits : 4*thread.val < 2^64 := by have := cfg.noWrap; have := thread.isLt; omega
  have double : (BitVec.ofNat 64 thread.val + BitVec.ofNat 64 thread.val : Address) =
      BitVec.ofNat 64 (2*thread.val) := by rw [← BitVec.ofNat_add]; congr 1; omega
  have four : (BitVec.ofNat 64 (2*thread.val) + BitVec.ofNat 64 (2*thread.val) : Address) =
      bytePointer thread.val := by rw [← BitVec.ofNat_add]; simp [bytePointer]; congr 1; omega
  have gi : addressIndex s.global (bytePointer thread.val) = .ok thread.val := by
    simp [addressIndex, bytePointer, Nat.mod_eq_of_lt pfits, show thread.val < s.global.length by have := thread.isLt; omega]
  have si : addressIndex s.shared (bytePointer thread.val) = .ok thread.val := by
    simp [addressIndex, bytePointer, Nat.mod_eq_of_lt pfits, show thread.val < s.shared.length by have := thread.isLt; omega]
  simp [run,runWith,List.replicate,step,dispatch,scalarStep,program,setLane,entry,
    producerStart,eval,Instr.plain,Guard.eval,Operand32.eval,Operand64.eval,update,
    Nat.mod_eq_of_lt fits,double,four,gi,si,sharedStore]
  intro other different
  simp [different]



def Ready (thread : Fin n) (lane : Lane) : Prop :=
  lane.block = .barrier ∧ lane.scalar.pc = 0 ∧
    lane.scalar.regs 0 = BitVec.ofNat 32 thread.val ∧ lane.halted = false

def producerSchedule (lanes : List (Fin n)) : List (Fin n) :=
  lanes.flatMap (List.replicate 7)

theorem producer_list (cfg : Config n) (s : State n) (seeds : Fin n → Seed)
    (lanes : List (Fin n)) (distinct : lanes.Nodup)
    (entry : ∀ lane ∈ lanes, s.lanes lane = ⟨.producer, producerStart s.global lane (seeds lane), false⟩)
    (inputs : n ≤ s.global.length) (storage : n ≤ s.shared.length) :
    let final := (run cfg (producerSchedule lanes) s).state
    final.global = s.global ∧
    final.shared = publishAll s.global seeds lanes s.shared ∧
    final.barrier = s.barrier ∧
    (∀ lane ∈ lanes, Ready lane (final.lanes lane)) ∧
    (∀ other, other ∉ lanes → final.lanes other = s.lanes other) := by
  induction lanes generalizing s with
  | nil => simp [producerSchedule,run,runWith,publishAll]
  | cons lane rest ih =>
    have unique := List.nodup_cons.mp distinct
    let mid := (run cfg (List.replicate 7 lane) s).state
    obtain ⟨globalEq, sharedEq, block, pc, value, live, barrierEq, others⟩ :=
      producer_phase cfg s lane (seeds lane) (entry lane (by simp)) inputs storage
    change mid.global = s.global at globalEq
    change mid.shared = _ at sharedEq
    have restEntry : ∀ other ∈ rest,
        mid.lanes other = ⟨.producer, producerStart mid.global other (seeds other), false⟩ := by
      intro other member
      have different : other ≠ lane := by intro h; subst other; exact unique.1 member
      rw [others other different,globalEq]
      exact entry other (by simp [member])
    have inductionResult := ih mid unique.2 restEntry (by simpa [globalEq] using inputs)
      (by rw [sharedEq]; simpa using storage)
    dsimp only at inductionResult
    simp only [producerSchedule, mid] at inductionResult
    simp only [producerSchedule,List.flatMap_cons] at ⊢
    rw [run_append]
    dsimp only
    change (run cfg (producerSchedule rest) mid).state.global = _ ∧ _
    refine ⟨inductionResult.1.trans globalEq, ?_, inductionResult.2.2.1.trans barrierEq, ?_, ?_⟩
    · rw [inductionResult.2.1,globalEq,sharedEq,publishAll_cons cfg s.global s.shared seeds lane rest inputs storage]
    · intro other member
      rcases List.mem_cons.mp member with same | tail
      · subst other
        rw [inductionResult.2.2.2.2 lane unique.1]
        exact ⟨block,pc,value,live⟩
      · exact inductionResult.2.2.2.1 other tail
    · intro other absent
      have different : other ≠ lane := by intro h; subst other; exact absent (by simp)
      have outside : other ∉ rest := by intro h; exact absent (by simp [h])
      exact (inductionResult.2.2.2.2 other outside).trans (others other different)

theorem producer_round (cfg : Config n) (input scratch : List Word) (seeds : Fin n → Seed)
    (inputs : n ≤ input.length) (storage : n ≤ scratch.length) :
    let final := (run cfg (producerSchedule (List.finRange n)) (start input scratch seeds)).state
    final.global = input ∧ final.shared = input.take n ++ scratch.drop n ∧
    final.barrier = Barrier.initial ∧ ∀ lane, Ready lane (final.lanes lane) := by
  have h := producer_list cfg (start input scratch seeds) seeds (List.finRange n)
    (List.nodup_finRange n) (fun _ _ => rfl) inputs storage
  dsimp only at h ⊢
  refine ⟨h.1, ?_, h.2.2.1, fun lane => h.2.2.2.1 lane (List.mem_finRange lane)⟩
  exact h.2.1.trans (publication_all cfg input scratch seeds inputs storage)

end Ptx.Scalar.SharedReduction.Machine

import Ptx.SharedReductionMachine

/-! Reachable waiting-control and fetched instruction classification for the fixed
reduction program. Target qualification is separate from the numerical machine.
No memory visibility, general warp refinement, or scheduler fairness is claimed. -/
namespace Ptx.Scalar.SharedReduction.Machine.Control

def AtBarrier (lane : Lane) : Prop :=
  lane.block = .barrier ∧ lane.scalar.pc = 0 ∧ lane.halted = false

def Invariant (s : State n) : Prop :=
  ∀ thread, s.barrier.arrived thread = true → AtBarrier (s.lanes thread)

theorem initial (input scratch : List Word) (seeds : Fin n → Seed) :
    Invariant (start input scratch seeds) := by
  simp [Invariant,start,Barrier.initial,Barrier.reset]

theorem fetch_sync (block : Block) (pc : Nat) (resource : Fin 16)
    (fetch : (program n block)[pc]? = some (.sync resource)) :
    block = .barrier ∧ pc = 0 ∧ resource = 0 := by
  have member := List.mem_of_getElem? fetch
  cases block <;> simp [program] at member
  subst resource
  simpa [program,List.getElem?_cons] using fetch

/-- Marked threads stay at the fetched barrier and cannot advance themselves. -/
theorem waiting_step_unchanged (cfg : Config n) (reads : Option Word)
    (s : State n) (thread : Fin n) (invariant : Invariant s)
    (waiting : s.barrier.arrived thread = true) :
    step cfg reads thread s = ⟨s,.waiting,[]⟩ := by
  obtain ⟨block,pc,live⟩ := invariant thread waiting
  have duplicate := Barrier.duplicate_wait_unchanged (barrierConfig cfg) s.barrier
    (barrierRequest cfg s thread 0) rfl waiting
  simp [step,live,block,pc,program,dispatch,duplicate]

private theorem transfer (s next : State n) (thread : Fin n)
    (invariant : Invariant s) (fresh : s.barrier.arrived thread = false)
    (same : next.barrier = s.barrier)
    (others : ∀ other, other ≠ thread → next.lanes other = s.lanes other) : Invariant next := by
  intro other arrived
  rw [same] at arrived
  have different : other ≠ thread := by intro h; subst other; simp [fresh] at arrived
  rw [others other different]
  exact invariant other arrived

private theorem scalar_preserves (reads : Option Word) (thread : Fin n)
    (space : Option Space) (instruction : Instr) (s : State n)
    (invariant : Invariant s) (fresh : s.barrier.arrived thread = false) :
    Invariant (scalarStep reads thread space instruction s).state := by
  cases space with
  | none =>
    simp only [scalarStep]
    split
    · exact transfer s _ thread invariant fresh rfl (fun _ h => setLane_other _ _ _ _ h)
    · exact transfer s _ thread invariant fresh rfl (fun _ h => setLane_other _ _ _ _ h)
    · exact invariant
    · exact invariant
  | some space =>
    cases space <;> simp only [scalarStep] <;> split
    all_goals first
      | exact transfer s _ thread invariant fresh rfl (fun _ h => setLane_other _ _ _ _ h)
      | exact invariant

private theorem sync_preserves (cfg : Config n) (reads : Option Word)
    (s : State n) (thread : Fin n) (invariant : Invariant s)
    (atBarrier : AtBarrier (s.lanes thread)) :
    Invariant (dispatch cfg reads thread (.sync 0) s).state := by
  by_cases waiting : s.barrier.arrived thread = true
  · simpa [dispatch,Barrier.step,barrierRequest,barrierConfig,Barrier.key,waiting] using invariant
  · by_cases complete : Barrier.Complete (Barrier.mark s.barrier thread)
    · simp [dispatch,Barrier.step,barrierRequest,barrierConfig,Barrier.key,waiting,complete,
        Invariant,Barrier.reset]
    · simp only [dispatch,Barrier.step,barrierRequest,barrierConfig,Barrier.key,waiting,complete,
        ↓reduceIte]
      intro other arrived
      change (Barrier.mark s.barrier thread).arrived other = true at arrived
      by_cases eq : other = thread
      · subst other; exact atBarrier
      · exact invariant other (by simpa [Barrier.mark,eq] using arrived)

theorem step_preserves (cfg : Config n) (reads : Option Word) (thread : Fin n)
    (s : State n) (invariant : Invariant s) :
    Invariant (step cfg reads thread s).state := by
  by_cases waiting : s.barrier.arrived thread = true
  · rw [waiting_step_unchanged cfg reads s thread invariant waiting]
    exact invariant
  have fresh : s.barrier.arrived thread = false := Bool.eq_false_iff.mpr waiting
  simp only [step]
  split
  · exact invariant
  · rename_i live
    have alive : (s.lanes thread).halted = false := Bool.eq_false_iff.mpr live
    split
    · exact invariant
    · rename_i instruction fetch
      cases instruction with
      | localStep i => exact scalar_preserves reads thread none i s invariant fresh
      | memory space i => exact scalar_preserves reads thread (some space) i s invariant fresh
      | branch guard destination =>
        refine transfer s (dispatch cfg reads thread (.branch guard destination) s).state thread invariant fresh rfl ?_
        intro other different
        simp [dispatch,setLane,different]
      | exit =>
        refine transfer s (dispatch cfg reads thread .exit s).state thread invariant fresh rfl ?_
        intro other different
        simp [dispatch,setLane,different]
      | sync resource =>
        obtain ⟨block,pc,rfl⟩ := fetch_sync _ _ _ fetch
        exact sync_preserves cfg reads s thread invariant ⟨block,pc,alive⟩

theorem runWith_preserves (cfg : Config n) (reads : Nat → Option Word)
    (schedule : List (Fin n)) (s : State n) (invariant : Invariant s) :
    Invariant (runWith cfg reads schedule s).state := by
  induction schedule generalizing reads s with
  | nil => exact invariant
  | cons thread rest ih => exact ih _ _ (step_preserves cfg (reads 0) thread s invariant)

/-- Completion cannot move a not-yet-arrived thread past its work. -/
theorem release_all_at_barrier (cfg : Config n) (reads : Option Word)
    (s : State n) (thread : Fin n) (invariant : Invariant s)
    (released : (step cfg reads thread s).status = .released) :
    ∀ other, AtBarrier (s.lanes other) := by
  simp only [step] at released
  split at released
  · contradiction
  · rename_i live
    have alive : (s.lanes thread).halted = false := Bool.eq_false_iff.mpr live
    split at released
    · contradiction
    · rename_i instruction fetch
      cases instruction with
      | localStep i =>
        simp only [dispatch,scalarStep] at released
        split at released <;> contradiction
      | memory space i =>
        cases space <;> simp only [dispatch,scalarStep] at released <;>
          split at released <;> contradiction
      | branch guard destination => simp [dispatch] at released
      | exit => simp [dispatch] at released
      | sync resource =>
        have disposition : (Barrier.step (barrierConfig cfg) s.barrier
            (barrierRequest cfg s thread resource)).disposition = .released := by
          cases h : (Barrier.step (barrierConfig cfg) s.barrier
            (barrierRequest cfg s thread resource)).disposition <;>
            simp_all [dispatch]
        obtain ⟨block,pc,resourceEq⟩ := fetch_sync _ _ _ fetch
        have complete := (Barrier.released_iff _ _ _).mp disposition |>.2.2
        intro other
        by_cases eq : other = thread
        · subst other; exact ⟨block,pc,alive⟩
        · exact invariant other (by simpa [Barrier.Waiting,Barrier.mark,barrierRequest,eq] using complete other)

/-- The release premise is an observed step; waiting-site facts are derived from
initialization and the arbitrary preceding candidate execution. -/
theorem reachable_release (cfg : Config n) (reads : Nat → Option Word)
    (schedule : List (Fin n)) (input scratch : List Word) (seeds : Fin n → Seed)
    (nextRead : Option Word) (thread : Fin n)
    (released : (step cfg nextRead thread
      (runWith cfg reads schedule (start input scratch seeds)).state).status = .released) :
    ∀ other, AtBarrier ((runWith cfg reads schedule (start input scratch seeds)).state.lanes other) :=
  release_all_at_barrier cfg nextRead _ thread
    (runWith_preserves cfg reads schedule _ (initial input scratch seeds)) released


/-- Classify the actual opcode, independently of its wrapper's space label. -/
def memoryKind : Scalar.Op → Option MemoryKind
  | .load _ _ => some .load
  | .store _ _ => some .store
  | _ => none

theorem fetched_classification (block : Block) (pc : Nat) (instruction : Instruction)
    (fetch : (program n block)[pc]? = some instruction) :
    match instruction with
    | .localStep i => memoryKind i.op = none
    | .memory _ i => (memoryKind i.op).isSome = true
    | _ => True := by
  have member := List.mem_of_getElem? fetch
  cases block <;> simp [program] at member
  all_goals rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first | rfl | trivial

/-- Target-neutral execution has a separately checked PTX feature boundary. -/
def SupportedTarget (target : Target) : Prop := target.isa = 94 ∧ 70 ≤ target.sm

def form (space : Space) (kind : AccessKind) : MemoryForm :=
  ⟨kind, (match space with | .global => .global | .shared => .shared),
    some (match space with | .global => .gpu | .shared => .cta), false⟩

theorem forms_eligible (target : Target) (supported : SupportedTarget target)
    (space : Space) (kind : AccessKind) :
    memoryEligibility target (form space kind) = .supported := by
  obtain ⟨isa,sm⟩ := supported
  cases space <;> cases kind <;> simp [memoryEligibility,form,isa,show ¬target.sm < 10 by omega,
    show ¬target.sm < 70 by omega]

/-- Every emitted effect retains the evaluated opcode and incoming PC. -/
theorem eval_effect_origin (reads : Option Word) (i : Instr) (s next : Scalar.State)
    (event : Occurrence) (effect : MemoryEffect)
    (evaluated : eval reads i s = .next next event) (memory : event.memory = some effect) :
    event.instruction = i ∧ event.pc = s.pc ∧ event.executed = true ∧
      memoryKind i.op = some effect.kind := by
  rcases i with ⟨guard,op⟩
  cases op <;> cases enabled : guard.eval s <;>
    simp only [eval,enabled,↓reduceIte] at evaluated
  all_goals first
    | (obtain ⟨_,rfl⟩ := StepResult.next.inj evaluated; simp [occurrence] at memory)
    | contradiction
    | skip
  all_goals
    split at evaluated
    · contradiction
    · obtain ⟨_,rfl⟩ := StepResult.next.inj evaluated
      simp only [occurrence,Option.some.injEq] at memory
      subst effect
      exact ⟨rfl,rfl,rfl,rfl⟩

/-- Scalar wrapper events retain the scheduled lane, selected arena and evaluated instruction. -/
theorem scalar_effect_origin (reads : Option Word) (thread : Fin n)
    (space : Option Space) (i : Instr) (s : State n)
    (seenThread : Fin n) (block : Block) (seenSpace : Option Space)
    (event : Occurrence) (effect : MemoryEffect)
    (member : .scalar seenThread block seenSpace event ∈ (scalarStep reads thread space i s).events)
    (memory : event.memory = some effect) :
    seenThread = thread ∧ block = (s.lanes thread).block ∧ seenSpace = space ∧
      event.instruction = i ∧ event.pc = (s.lanes thread).scalar.pc ∧
      event.executed = true ∧ memoryKind i.op = some effect.kind := by
  rcases space with _ | (_ | _)
  all_goals
    simp only [scalarStep] at member
    split at member
    · rename_i next emitted evaluated
      simp only [List.mem_singleton,Event.scalar.injEq] at member
      obtain ⟨rfl,rfl,rfl,rfl⟩ := member
      have origin := eval_effect_origin reads i _ next _ effect evaluated memory
      exact ⟨rfl,rfl,rfl,origin⟩
    · rename_i next emitted evaluated
      simp only [List.mem_singleton,Event.scalar.injEq] at member
      obtain ⟨rfl,rfl,rfl,rfl⟩ := member
      have empty := (Scalar.eval_halted evaluated).2
      rw [empty] at memory
      contradiction
    · simp at member
    · simp at member

/-- No actual memory effect is lost by filtering scalar events to their stated space. -/
theorem step_memory_origin (cfg : Config n) (reads : Option Word) (thread : Fin n)
    (s : State n) (seenThread : Fin n) (block : Block) (space : Option Space)
    (event : Occurrence) (effect : MemoryEffect)
    (member : .scalar seenThread block space event ∈ (step cfg reads thread s).events)
    (memory : event.memory = some effect) :
    ∃ actualSpace, space = some actualSpace ∧
      (program n block)[event.pc]? = some (.memory actualSpace event.instruction) ∧
      event.executed = true ∧ memoryKind event.instruction.op = some effect.kind := by
  simp only [step] at member
  split at member
  · simp at member
  · split at member
    · simp at member
    · rename_i instruction fetch
      cases instruction with
      | localStep i =>
        have origin := scalar_effect_origin reads thread none i s seenThread block space event effect member memory
        have noMemory := fetched_classification _ _ _ fetch
        rw [noMemory] at origin
        simp at origin
      | memory actualSpace i =>
        obtain ⟨rfl,rfl,rfl,hi,hpc,enabled,kind⟩ :=
          scalar_effect_origin reads thread (some actualSpace) i s seenThread block space event effect member memory
        exact ⟨actualSpace,rfl,by simpa [hi,hpc] using fetch,enabled,by simpa [hi] using kind⟩
      | branch guard destination => simp [dispatch] at member
      | exit => simp [dispatch] at member
      | sync resource =>
        simp only [dispatch] at member
        split at member <;> simp only [List.mem_map] at member
        · simp at member
        all_goals obtain ⟨_,_,impossible⟩ := member; contradiction

/-- Arbitrary candidate read choices and schedules preserve complete memory-event origin. -/
theorem runWith_memory_origin (cfg : Config n) (reads : Nat → Option Word)
    (schedule : List (Fin n)) (s : State n) (thread : Fin n) (block : Block)
    (space : Option Space) (event : Occurrence) (effect : MemoryEffect)
    (member : .scalar thread block space event ∈ (runWith cfg reads schedule s).trace)
    (memory : event.memory = some effect) :
    ∃ actualSpace, space = some actualSpace ∧
      (program n block)[event.pc]? = some (.memory actualSpace event.instruction) ∧
      event.executed = true ∧ memoryKind event.instruction.op = some effect.kind := by
  induction schedule generalizing reads s with
  | nil => simp [runWith] at member
  | cons selected rest ih =>
    simp only [runWith,List.mem_append] at member
    rcases member with first | later
    · exact step_memory_origin cfg (reads 0) selected s thread block space event effect first memory
    · exact ih _ _ later

/-- The only fetched global store uses the fixed, separate output byte address. -/
theorem fetched_global_store (block : Block) (pc : Nat) (i : Instr)
    (fetch : (program n block)[pc]? = some (.memory .global i))
    (store : memoryKind i.op = some .store) :
    i = Instr.plain (.store (.imm (bytePointer n)) (.reg 1)) := by
  have member := List.mem_of_getElem? fetch
  cases block <;> simp [program] at member
  all_goals subst i
  · simp [memoryKind,Instr.plain] at store
  · rfl

private theorem eval_store_address (reads : Option Word) (i : Instr)
    (s next : Scalar.State) (event : Occurrence) (effect : MemoryEffect)
    (pointer : Address) (source : Operand32)
    (opcode : i.op = .store (.imm pointer) source)
    (evaluated : eval reads i s = .next next event) (memory : event.memory = some effect) :
    effect.address = pointer := by
  rcases i with ⟨guard,op⟩
  dsimp only at opcode
  subst op
  cases enabled : guard.eval s <;> simp only [eval,enabled,↓reduceIte] at evaluated
  · obtain ⟨_,rfl⟩ := StepResult.next.inj evaluated
    simp [occurrence] at memory
  · split at evaluated
    · contradiction
    · obtain ⟨_,rfl⟩ := StepResult.next.inj evaluated
      simpa [occurrence,Operand64.eval] using (congrArg (fun x => x.map MemoryEffect.address) memory).symm

private theorem scalar_store_address (reads : Option Word) (thread : Fin n)
    (space : Option Space) (i : Instr) (s : State n)
    (seenThread : Fin n) (block : Block) (seenSpace : Option Space)
    (event : Occurrence) (effect : MemoryEffect) (pointer : Address) (source : Operand32)
    (opcode : i.op = .store (.imm pointer) source)
    (member : .scalar seenThread block seenSpace event ∈ (scalarStep reads thread space i s).events)
    (memory : event.memory = some effect) : effect.address = pointer := by
  rcases space with _ | (_ | _)
  all_goals
    simp only [scalarStep] at member
    split at member
    · rename_i next emitted evaluated
      simp only [List.mem_singleton,Event.scalar.injEq] at member
      obtain ⟨rfl,rfl,rfl,rfl⟩ := member
      exact eval_store_address reads i _ next _ effect pointer source opcode evaluated memory
    · rename_i next emitted evaluated
      simp only [List.mem_singleton,Event.scalar.injEq] at member
      obtain ⟨rfl,rfl,rfl,rfl⟩ := member
      rw [(Scalar.eval_halted evaluated).2] at memory
      contradiction
    · simp at member
    · simp at member

theorem step_global_store_address (cfg : Config n) (reads : Option Word) (selected : Fin n)
    (s : State n) (thread : Fin n) (block : Block) (event : Occurrence) (effect : MemoryEffect)
    (member : .scalar thread block (some .global) event ∈ (step cfg reads selected s).events)
    (memory : event.memory = some effect) (store : effect.kind = .store) :
    effect.address = bytePointer n := by
  simp only [step] at member
  split at member
  · simp at member
  · split at member
    · simp at member
    · rename_i instruction fetch
      cases instruction with
      | localStep i =>
        have origin := scalar_effect_origin reads selected none i s thread block (some .global) event effect member memory
        simp at origin
      | memory actualSpace i =>
        have origin := scalar_effect_origin reads selected (some actualSpace) i s thread block (some .global) event effect member memory
        have spaceEq : actualSpace = .global := by simpa using origin.2.2.1.symm
        subst actualSpace
        have opcode := fetched_global_store _ _ i fetch (by simpa [store] using origin.2.2.2.2.2.2)
        exact scalar_store_address reads selected (some .global) i s thread block (some .global)
          event effect (bytePointer n) (.reg 1) (by simp [opcode,Instr.plain]) member memory
      | branch guard destination => simp [dispatch] at member
      | exit => simp [dispatch] at member
      | sync resource =>
        simp only [dispatch] at member
        split at member <;> simp only [List.mem_map] at member
        · simp at member
        all_goals obtain ⟨_,_,impossible⟩ := member; contradiction

theorem runWith_global_store_address (cfg : Config n) (reads : Nat → Option Word)
    (schedule : List (Fin n)) (s : State n) (thread : Fin n) (block : Block)
    (event : Occurrence) (effect : MemoryEffect)
    (member : .scalar thread block (some .global) event ∈ (runWith cfg reads schedule s).trace)
    (memory : event.memory = some effect) (store : effect.kind = .store) :
    effect.address = bytePointer n := by
  induction schedule generalizing reads s with
  | nil => simp [runWith] at member
  | cons selected rest ih =>
    simp only [runWith,List.mem_append] at member
    rcases member with first | later
    · exact step_global_store_address cfg (reads 0) selected s thread block event effect first memory store
    · exact ih _ _ later

end Ptx.Scalar.SharedReduction.Machine.Control

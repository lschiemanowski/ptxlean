import Ptx.SharedReductionData

namespace Ptx.Scalar.SharedReduction.Machine.Data

/-- A value has an actual earlier producer-load event. This does not assert that
it equals initialized memory; the candidate memory model supplies that obligation. -/
def Recorded (history : List (Event n)) (thread : Fin n) (value : Word) : Prop :=
  ∃ event address, .scalar thread .producer (some .global) event ∈ history ∧
    event.memory = some ⟨.load,address,value⟩

@[simp] theorem recorded_append (left right : List (Event n)) (thread : Fin n) (value : Word) :
    Recorded (left ++ right) thread value ↔ Recorded left thread value ∨ Recorded right thread value := by
  constructor
  · rintro ⟨event,address,member,memory⟩
    rcases List.mem_append.mp member with before | after
    · exact Or.inl ⟨event,address,before,memory⟩
    · exact Or.inr ⟨event,address,after,memory⟩
  · rintro (⟨event,address,member,memory⟩ | ⟨event,address,member,memory⟩)
    · exact ⟨event,address,List.mem_append_left _ member,memory⟩
    · exact ⟨event,address,List.mem_append_right _ member,memory⟩

def LaneValueInvariant (history : List (Event n)) (thread : Fin n) (lane : Lane) : Prop :=
  match lane.block with
  | .producer => lane.scalar.pc = 4 → Recorded history thread (lane.scalar.regs 1)
  | .publish | .barrier | .choose => Recorded history thread (lane.scalar.regs 1)
  | _ => True

def ValueInvariant (history : List (Event n)) (s : State n) : Prop :=
  ∀ thread, LaneValueInvariant history thread (s.lanes thread)

theorem value_initial (input scratch : List Word) (seeds : Fin n → Seed) :
    ValueInvariant [] (start input scratch seeds) := by
  intro thread
  simp [LaneValueInvariant,start,producerStart]

theorem value_extend (history extra : List (Event n)) (thread : Fin n) (lane : Lane)
    (old : LaneValueInvariant history thread lane) :
    LaneValueInvariant (history ++ extra) thread lane := by
  cases block : lane.block <;> simp only [LaneValueInvariant,block] at old ⊢
  · intro pc; exact (recorded_append _ _ _ _).mpr (.inl (old pc))
  all_goals first | trivial | exact (recorded_append _ _ _ _).mpr (.inl old)

set_option maxHeartbeats 800000 in
private theorem selected_value_preserves (cfg : Config n) (reads : Option Word)
    (s : State n) (thread : Fin n) (history : List (Event n))
    (data : LaneValueInvariant history thread (s.lanes thread)) :
    LaneValueInvariant (history ++ (step cfg reads thread s).events) thread
      ((step cfg reads thread s).state.lanes thread) := by
  have extended := value_extend history (step cfg reads thread s).events thread (s.lanes thread) data
  by_cases stopped : (s.lanes thread).halted = true
  · simpa [step,stopped] using extended
  have alive : (s.lanes thread).halted = false := Bool.eq_false_iff.mpr stopped
  cases hb : (s.lanes thread).block
  all_goals rcases hp : (s.lanes thread).scalar.pc with _ | _ | _ | _ | _ | _ | _ | _ | k
  all_goals cases pred : (s.lanes thread).scalar.preds 0
  all_goals simp only [LaneValueInvariant,hb,hp] at data extended
  all_goals simp [step,alive,hb,hp,program,dispatch,scalarStep,eval,Instr.plain,Guard.eval,
    Operand32.eval,Operand64.eval,setLane,LaneValueInvariant,sharedStore,pred]
  all_goals try {
    cases disposition : (Barrier.step (barrierConfig cfg) s.barrier
      (barrierRequest cfg s thread 0)).disposition <;> simp_all }
  all_goals cases address : addressIndex s.shared ((s.lanes thread).scalar.addrs 0)
  all_goals cases globalAddress : addressIndex s.global ((s.lanes thread).scalar.addrs 0)
  all_goals cases outputAddress : addressIndex s.global (bytePointer n)
  all_goals try simp_all [update]
  all_goals simp [Recorded,occurrence]

/-- The recorded load is preserved through arbitrary interleavings; a barrier
release changes continuation labels, not the published value register. -/
theorem value_step_preserves (cfg : Config n) (reads : Option Word) (s : State n)
    (thread : Fin n) (history : List (Event n))
    (control : Control.Invariant s) (data : ValueInvariant history s) :
    ValueInvariant (history ++ (step cfg reads thread s).events) (step cfg reads thread s).state := by
  intro other
  by_cases released : (step cfg reads thread s).status = .released
  · rw [release_lane_fields cfg reads s thread other released]
    have atSite := Control.release_all_at_barrier cfg reads s thread control released other
    have h := value_extend history (step cfg reads thread s).events other _ (data other)
    simpa only [LaneValueInvariant,atSite.1] using h
  · by_cases same : other = thread
    · subst other; exact selected_value_preserves cfg reads s thread history (data thread)
    · rw [step_other cfg reads s thread other same released]
      exact value_extend history (step cfg reads thread s).events other _ (data other)

theorem value_runWith_preserves (cfg : Config n) (reads : Nat → Option Word)
    (schedule : List (Fin n)) (s : State n) (history : List (Event n))
    (control : Control.Invariant s) (data : ValueInvariant history s) :
    ValueInvariant (history ++ (runWith cfg reads schedule s).trace)
      (runWith cfg reads schedule s).state := by
  induction schedule generalizing reads s history with
  | nil => simpa [runWith] using data
  | cons thread rest ih =>
    have later := ih (fun i => reads (i+1)) (step cfg (reads 0) thread s).state
      (history ++ (step cfg (reads 0) thread s).events)
      (Control.step_preserves cfg (reads 0) thread s control)
      (value_step_preserves cfg (reads 0) s thread history control data)
    simpa only [runWith,List.append_assoc] using later

theorem value_reachable (cfg : Config n) (reads : Nat → Option Word) (schedule : List (Fin n))
    (input scratch : List Word) (seeds : Fin n → Seed) :
    ValueInvariant (runWith cfg reads schedule (start input scratch seeds)).trace
      (runWith cfg reads schedule (start input scratch seeds)).state := by
  simpa only [List.nil_append] using value_runWith_preserves cfg reads schedule _ []
    (Control.initial input scratch seeds) (value_initial input scratch seeds)

private theorem fetched_shared_store (block : Block) (pc : Nat) (i : Instr)
    (fetch : (program n block)[pc]? = some (.memory .shared i))
    (store : Control.memoryKind i.op = some .store) : block = .publish ∧ i = sharedStore := by
  have member := List.mem_of_getElem? fetch
  cases block <;> simp [program] at member
  all_goals subst i
  · exact ⟨rfl,rfl⟩
  · simp [Control.memoryKind,Instr.plain] at store

private theorem scalar_shared_store_value (reads : Option Word) (selected : Fin n) (s : State n)
    (thread : Fin n) (block : Block) (event : Occurrence) (effect : MemoryEffect)
    (member : .scalar thread block (some .shared) event ∈
      (scalarStep reads selected (some .shared) sharedStore s).events)
    (memory : event.memory = some effect) : effect.value = (s.lanes selected).scalar.regs 1 := by
  cases address : addressIndex s.shared ((s.lanes selected).scalar.addrs 0) <;>
    simp [scalarStep,sharedStore,Instr.plain,eval,Guard.eval,Operand64.eval,address] at member
  obtain ⟨rfl,rfl,rfl⟩ := member
  simpa [occurrence,Operand32.eval] using
    (congrArg (fun x => x.map MemoryEffect.value) memory).symm

/-- A publication uses the recorded pre-step register value, never an assumed
initialized input or desired output. -/
theorem step_shared_store_recorded (cfg : Config n) (reads : Option Word) (selected : Fin n)
    (s : State n) (history : List (Event n)) (thread : Fin n) (block : Block)
    (event : Occurrence) (effect : MemoryEffect) (data : ValueInvariant history s)
    (member : .scalar thread block (some .shared) event ∈ (step cfg reads selected s).events)
    (memory : event.memory = some effect) (store : effect.kind = .store) :
    Recorded history thread effect.value := by
  simp only [step] at member
  split at member
  · simp at member
  · split at member
    · simp at member
    · rename_i instruction fetch
      cases instruction with
      | localStep i =>
        have origin := Control.scalar_effect_origin reads selected none i s thread block (some .shared) event effect member memory
        simp at origin
      | memory actualSpace i =>
        have origin := Control.scalar_effect_origin reads selected (some actualSpace) i s thread block (some .shared) event effect member memory
        have spaceEq : actualSpace = .shared := by simpa using origin.2.2.1.symm
        subst actualSpace
        obtain ⟨atPublish,rfl⟩ := fetched_shared_store _ _ i fetch
          (by simpa [store] using origin.2.2.2.2.2.2)
        have value := scalar_shared_store_value reads selected s thread block event effect member memory
        have known := data selected
        simpa only [LaneValueInvariant,atPublish,origin.1,value] using known
      | branch guard destination => simp [dispatch] at member
      | exit => simp [dispatch] at member
      | sync resource =>
        simp only [dispatch] at member
        split at member <;> simp only [List.mem_map] at member
        · simp at member
        all_goals obtain ⟨_,_,impossible⟩ := member; contradiction

/-- At any reachable next publication, its supplying global load is in the
strictly earlier trace prefix, including under arbitrary candidate reads. -/
theorem reachable_shared_store_recorded (cfg : Config n) (reads : Nat → Option Word)
    (schedule : List (Fin n)) (input scratch : List Word) (seeds : Fin n → Seed)
    (nextRead : Option Word) (selected thread : Fin n) (block : Block)
    (event : Occurrence) (effect : MemoryEffect)
    (member : .scalar thread block (some .shared) event ∈
      (step cfg nextRead selected (runWith cfg reads schedule (start input scratch seeds)).state).events)
    (memory : event.memory = some effect) (store : effect.kind = .store) :
    Recorded (runWith cfg reads schedule (start input scratch seeds)).trace thread effect.value :=
  step_shared_store_recorded cfg nextRead selected _ _ thread block event effect
    (value_reachable cfg reads schedule input scratch seeds) member memory store

/-- A whole-trace memory consumer can recover the supplying load without
knowing the scheduler's decomposition. The prefix theorem above supplies order. -/
theorem runWith_shared_store_recorded (cfg : Config n) (reads : Nat → Option Word)
    (schedule : List (Fin n)) (s : State n) (history : List (Event n))
    (thread : Fin n) (block : Block) (event : Occurrence) (effect : MemoryEffect)
    (control : Control.Invariant s) (data : ValueInvariant history s)
    (member : .scalar thread block (some .shared) event ∈ (runWith cfg reads schedule s).trace)
    (memory : event.memory = some effect) (store : effect.kind = .store) :
    Recorded (history ++ (runWith cfg reads schedule s).trace) thread effect.value := by
  induction schedule generalizing reads s history with
  | nil => simp [runWith] at member
  | cons selected rest ih =>
    simp only [runWith,List.mem_append] at member
    rcases member with first | later
    · exact (recorded_append _ _ _ _).mpr (.inl
        (step_shared_store_recorded cfg (reads 0) selected s history thread block event effect data first memory store))
    · have h := ih _ _ (history ++ (step cfg (reads 0) selected s).events)
        (Control.step_preserves cfg (reads 0) selected s control)
        (value_step_preserves cfg (reads 0) s selected history control data) later
      simpa only [runWith,List.append_assoc] using h

/-- Every actual shared publication follows an actual producer load of exactly
its stored value in the same finite trace; the load is strictly earlier. -/
theorem runWith_shared_store_path (cfg : Config n) (reads : Nat → Option Word)
    (schedule : List (Fin n)) (s : State n) (history : List (Event n))
    (thread : Fin n) (block : Block) (event : Occurrence) (effect : MemoryEffect)
    (control : Control.Invariant s) (data : ValueInvariant history s)
    (member : .scalar thread block (some .shared) event ∈ (runWith cfg reads schedule s).trace)
    (memory : event.memory = some effect) (store : effect.kind = .store) :
    ∃ load address, load.memory = some ⟨.load,address,effect.value⟩ ∧
      [.scalar thread .producer (some .global) load, .scalar thread block (some .shared) event].Sublist
        (history ++ (runWith cfg reads schedule s).trace) := by
  induction schedule generalizing reads s history with
  | nil => simp [runWith] at member
  | cons selected rest ih =>
    simp only [runWith,List.mem_append] at member
    rcases member with first | later
    · obtain ⟨load,address,earlier,loadMemory⟩ :=
        step_shared_store_recorded cfg (reads 0) selected s history thread block event effect data first memory store
      refine ⟨load,address,loadMemory,?_⟩
      have path := (List.singleton_sublist.mpr earlier).append
        ((List.singleton_sublist.mpr first).trans (List.sublist_append_left _
          (runWith cfg (fun i => reads (i+1)) rest (step cfg (reads 0) selected s).state).trace))
      simpa only [runWith,List.cons_append,List.nil_append] using path
    · obtain ⟨load,address,loadMemory,path⟩ := ih _ _
        (history ++ (step cfg (reads 0) selected s).events)
        (Control.step_preserves cfg (reads 0) selected s control)
        (value_step_preserves cfg (reads 0) s selected history control data) later
      exact ⟨load,address,loadMemory,by simpa only [runWith,List.append_assoc] using path⟩

theorem shared_store_path (cfg : Config n) (reads : Nat → Option Word)
    (schedule : List (Fin n)) (input scratch : List Word) (seeds : Fin n → Seed)
    (thread : Fin n) (block : Block) (event : Occurrence) (effect : MemoryEffect)
    (member : .scalar thread block (some .shared) event ∈
      (runWith cfg reads schedule (start input scratch seeds)).trace)
    (memory : event.memory = some effect) (store : effect.kind = .store) :
    ∃ load address, load.memory = some ⟨.load,address,effect.value⟩ ∧
      [.scalar thread .producer (some .global) load, .scalar thread block (some .shared) event].Sublist
        (runWith cfg reads schedule (start input scratch seeds)).trace := by
  simpa only [List.nil_append] using runWith_shared_store_path cfg reads schedule _ []
    thread block event effect (Control.initial input scratch seeds)
    (value_initial input scratch seeds) member memory store

end Ptx.Scalar.SharedReduction.Machine.Data

import Ptx.SharedReductionControl

namespace Ptx.Scalar.SharedReduction.Machine.Data

/-- Only producer-stage registers are constrained; later leader registers are
changed by their own fetched instructions and are not claimed to retain lane IDs. -/
def LaneInvariant (thread : Fin n) (lane : Lane) : Prop :=
  match lane.block with
  | .producer => lane.scalar.regs 0 = BitVec.ofNat 32 thread.val ∧
      (lane.scalar.pc = 1 → lane.scalar.addrs 0 = BitVec.ofNat 64 thread.val) ∧
      (lane.scalar.pc = 2 → lane.scalar.addrs 0 = BitVec.ofNat 64 (2*thread.val)) ∧
      (lane.scalar.pc = 3 ∨ lane.scalar.pc = 4 → lane.scalar.addrs 0 = bytePointer thread.val)
  | .publish | .barrier | .choose =>
      lane.scalar.regs 0 = BitVec.ofNat 32 thread.val ∧ lane.scalar.addrs 0 = bytePointer thread.val
  | _ => True

def Invariant (s : State n) : Prop := ∀ thread, LaneInvariant thread (s.lanes thread)

theorem initial (input scratch : List Word) (seeds : Fin n → Seed) :
    Invariant (start input scratch seeds) := by
  intro thread
  simp [LaneInvariant,start,producerStart,update]

/-- The dispatcher changes other lanes only on an actual collective release. -/
theorem step_other (cfg : Config n) (reads : Option Word) (s : State n) (thread other : Fin n)
    (different : other ≠ thread) (notReleased : (step cfg reads thread s).status ≠ .released) :
    (step cfg reads thread s).state.lanes other = s.lanes other := by
  simp only [step] at notReleased ⊢
  split
  · rfl
  · split
    · rfl
    · rename_i instruction fetch
      cases instruction with
      | localStep i =>
        simp only [dispatch,scalarStep] at notReleased ⊢
        split <;> simp [setLane,different]
      | memory space i =>
        cases space <;> simp only [dispatch,scalarStep] at notReleased ⊢ <;>
          split <;> simp [setLane,different]
      | branch guard destination => simp [dispatch,setLane,different]
      | exit => simp [dispatch,setLane,different]
      | sync resource =>
        simp only [dispatch] at notReleased ⊢
        split <;> simp_all

theorem release_lane_fields (cfg : Config n) (reads : Option Word) (s : State n) (thread other : Fin n)
    (released : (step cfg reads thread s).status = .released) :
    (step cfg reads thread s).state.lanes other =
      {s.lanes other with block := .choose,scalar := {(s.lanes other).scalar with pc := 0}} := by
  simp only [step] at released ⊢
  split at released
  · contradiction
  · rename_i live
    simp only [live]
    split at released
    · contradiction
    · rename_i instruction fetch
      cases instruction with
      | localStep i => simp only [dispatch,scalarStep] at released; split at released <;> contradiction
      | memory space i =>
        cases space <;> simp only [dispatch,scalarStep] at released <;> split at released <;> contradiction
      | branch guard destination => simp [dispatch] at released
      | exit => simp [dispatch] at released
      | sync resource =>
        simp only [dispatch] at released ⊢
        split at released <;> simp_all



set_option maxHeartbeats 800000 in
private theorem selected_preserves (cfg : Config n) (reads : Option Word)
    (s : State n) (thread : Fin n) (data : LaneInvariant thread (s.lanes thread)) :
    LaneInvariant thread ((step cfg reads thread s).state.lanes thread) := by
  have fits : thread.val < 2^32 := by have := cfg.noWrap; have := thread.isLt; omega
  have double : (BitVec.ofNat 64 thread.val + BitVec.ofNat 64 thread.val : Address) =
      BitVec.ofNat 64 (2*thread.val) := by rw [← BitVec.ofNat_add]; congr 1; omega
  have four : (BitVec.ofNat 64 (2*thread.val) + BitVec.ofNat 64 (2*thread.val) : Address) =
      bytePointer thread.val := by rw [← BitVec.ofNat_add]; simp [bytePointer]; congr 1; omega
  by_cases stopped : (s.lanes thread).halted = true
  · simpa [step,stopped] using data
  have alive : (s.lanes thread).halted = false := Bool.eq_false_iff.mpr stopped
  cases hb : (s.lanes thread).block
  all_goals rcases hp : (s.lanes thread).scalar.pc with _ | _ | _ | _ | _ | _ | _ | _ | k
  all_goals cases pred : (s.lanes thread).scalar.preds 0
  all_goals simp only [LaneInvariant,hb,hp] at data
  all_goals simp [step,alive,hb,hp,program,dispatch,scalarStep,eval,Instr.plain,Guard.eval,
    Operand32.eval,Operand64.eval,update,setLane,LaneInvariant,sharedStore,pred]
  all_goals try {
    cases disposition : (Barrier.step (barrierConfig cfg) s.barrier
      (barrierRequest cfg s thread 0)).disposition <;> simp_all }
  all_goals first
    | (cases address : addressIndex s.shared ((s.lanes thread).scalar.addrs 0) <;>
        simp_all)
    | skip
  all_goals cases globalAddress : addressIndex s.global ((s.lanes thread).scalar.addrs 0)
  all_goals cases outputAddress : addressIndex s.global (bytePointer n)
  all_goals try simp_all [update]
  all_goals try { split <;> simp_all [LaneInvariant] }

/-- All candidate observations and schedules preserve the producer's computed address. -/
theorem step_preserves (cfg : Config n) (reads : Option Word) (s : State n) (thread : Fin n)
    (control : Control.Invariant s) (data : Invariant s) :
    Invariant (step cfg reads thread s).state := by
  intro other
  by_cases released : (step cfg reads thread s).status = .released
  · rw [release_lane_fields cfg reads s thread other released]
    have atSite := Control.release_all_at_barrier cfg reads s thread control released other
    have h := data other
    simp only [LaneInvariant,atSite.1] at h
    exact h
  · by_cases same : other = thread
    · subst other; exact selected_preserves cfg reads s thread (data thread)
    · rw [step_other cfg reads s thread other same released]
      exact data other

theorem runWith_preserves (cfg : Config n) (reads : Nat → Option Word)
    (schedule : List (Fin n)) (s : State n) (control : Control.Invariant s) (data : Invariant s) :
    Invariant (runWith cfg reads schedule s).state := by
  induction schedule generalizing reads s with
  | nil => exact data
  | cons thread rest ih =>
    exact ih _ _ (Control.step_preserves cfg (reads 0) thread s control)
      (step_preserves cfg (reads 0) s thread control data)

theorem reachable (cfg : Config n) (reads : Nat → Option Word) (schedule : List (Fin n))
    (input scratch : List Word) (seeds : Fin n → Seed) :
    Invariant (runWith cfg reads schedule (start input scratch seeds)).state :=
  runWith_preserves cfg reads schedule _ (Control.initial input scratch seeds) (initial input scratch seeds)

private theorem eval_register_address (reads : Option Word) (i : Instr)
    (s next : Scalar.State) (event : Occurrence) (effect : MemoryEffect)
    (opcode : (∃ dest, i.op = .load dest (.reg 0)) ∨
      (∃ value, i.op = .store (.reg 0) value))
    (evaluated : eval reads i s = .next next event) (memory : event.memory = some effect) :
    effect.address = s.addrs 0 := by
  rcases i with ⟨guard,op⟩
  rcases opcode with ⟨dest,rfl⟩ | ⟨value,rfl⟩
  all_goals cases enabled : guard.eval s <;> simp only [eval,enabled,↓reduceIte] at evaluated
  all_goals first
    | (obtain ⟨_,rfl⟩ := StepResult.next.inj evaluated; simp [occurrence] at memory)
    | skip
  all_goals split at evaluated
  all_goals first | contradiction | skip
  all_goals obtain ⟨_,rfl⟩ := StepResult.next.inj evaluated
  all_goals simpa [occurrence,Operand64.eval] using
    (congrArg (fun x => x.map MemoryEffect.address) memory).symm

private theorem scalar_register_address (reads : Option Word) (selected : Fin n)
    (space : Space) (i : Instr) (s : State n) (thread : Fin n) (block : Block)
    (event : Occurrence) (effect : MemoryEffect)
    (opcode : (∃ dest, i.op = .load dest (.reg 0)) ∨
      (∃ value, i.op = .store (.reg 0) value))
    (member : .scalar thread block (some space) event ∈
      (scalarStep reads selected (some space) i s).events)
    (memory : event.memory = some effect) : effect.address = (s.lanes selected).scalar.addrs 0 := by
  cases space
  all_goals
    simp only [scalarStep] at member
    split at member
    · rename_i next emitted evaluated
      simp only [List.mem_singleton,Event.scalar.injEq] at member
      obtain ⟨rfl,rfl,_,rfl⟩ := member
      have address := eval_register_address reads i _ next _ effect opcode evaluated memory
      exact address
    · rename_i next emitted evaluated
      simp only [List.mem_singleton,Event.scalar.injEq] at member
      obtain ⟨rfl,rfl,_,rfl⟩ := member
      rw [(Scalar.eval_halted evaluated).2] at memory
      contradiction
    · simp at member
    · simp at member

private theorem fetched_producer_address (thread : Fin n) (lane : Lane) (i : Instr)
    (space : Space) (kind : MemoryKind) (data : LaneInvariant thread lane)
    (fetch : (program n lane.block)[lane.scalar.pc]? = some (.memory space i))
    (instructionKind : Control.memoryKind i.op = some kind)
    (producer : (space = .global ∧ kind = .load) ∨ (space = .shared ∧ kind = .store)) :
    lane.scalar.addrs 0 = bytePointer thread.val ∧
      ((∃ dest, i.op = .load dest (.reg 0)) ∨ (∃ value, i.op = .store (.reg 0) value)) := by
  cases hb : lane.block <;>
    rcases hp : lane.scalar.pc with _ | _ | _ | _ | _ | _ | _ | _ | k
  all_goals simp [program,hb,hp] at fetch
  all_goals obtain ⟨rfl,rfl⟩ := fetch
  all_goals simp only [sharedStore,Instr.plain,Control.memoryKind,Option.some.injEq] at instructionKind
  all_goals subst kind
  all_goals simp_all [LaneInvariant,sharedStore,Instr.plain]

/-- Producer input loads and publications use their issuer's computed slot. -/
theorem step_producer_address (cfg : Config n) (reads : Option Word) (selected : Fin n)
    (s : State n) (thread : Fin n) (block : Block) (space : Space)
    (event : Occurrence) (effect : MemoryEffect) (data : Invariant s)
    (member : .scalar thread block (some space) event ∈ (step cfg reads selected s).events)
    (memory : event.memory = some effect)
    (producer : (space = .global ∧ effect.kind = .load) ∨
      (space = .shared ∧ effect.kind = .store)) : effect.address = bytePointer thread.val := by
  simp only [step] at member
  split at member
  · simp at member
  · split at member
    · simp at member
    · rename_i instruction fetch
      cases instruction with
      | localStep i =>
        have origin := Control.scalar_effect_origin reads selected none i s thread block (some space) event effect member memory
        simp at origin
      | memory actualSpace i =>
        have origin := Control.scalar_effect_origin reads selected (some actualSpace) i s thread block (some space) event effect member memory
        have spaceEq : actualSpace = space := by simpa using origin.2.2.1.symm
        subst actualSpace
        obtain ⟨address,opcode⟩ := fetched_producer_address selected _ i space effect.kind
          (data selected) fetch origin.2.2.2.2.2.2 producer
        rw [scalar_register_address reads selected space i s thread block event effect opcode member memory,address,origin.1]
      | branch guard destination => simp [dispatch] at member
      | exit => simp [dispatch] at member
      | sync resource =>
        simp only [dispatch] at member
        split at member <;> simp only [List.mem_map] at member
        · simp at member
        all_goals obtain ⟨_,_,impossible⟩ := member; contradiction

theorem runWith_producer_address (cfg : Config n) (reads : Nat → Option Word)
    (schedule : List (Fin n)) (s : State n) (thread : Fin n) (block : Block) (space : Space)
    (event : Occurrence) (effect : MemoryEffect) (control : Control.Invariant s) (data : Invariant s)
    (member : .scalar thread block (some space) event ∈ (runWith cfg reads schedule s).trace)
    (memory : event.memory = some effect)
    (producer : (space = .global ∧ effect.kind = .load) ∨
      (space = .shared ∧ effect.kind = .store)) : effect.address = bytePointer thread.val := by
  induction schedule generalizing reads s with
  | nil => simp [runWith] at member
  | cons selected rest ih =>
    simp only [runWith,List.mem_append] at member
    rcases member with first | later
    · exact step_producer_address cfg (reads 0) selected s thread block space event effect data first memory producer
    · exact ih _ _ (Control.step_preserves cfg (reads 0) selected s control)
        (step_preserves cfg (reads 0) s selected control data) later

end Ptx.Scalar.SharedReduction.Machine.Data

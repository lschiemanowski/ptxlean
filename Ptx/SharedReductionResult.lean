import Ptx.SharedReductionValues
import Ptx.SharedReductionLoop

namespace Ptx.Scalar.SharedReduction.Machine.ResultProof

/-- A condition on actual emitted reads, later discharged by the combined
candidate graph. It does not assert a final accumulator or output. -/
def ReadContract (n : Nat) (input : List Word) (trace : List (Event n)) : Prop :=
  ∀ thread block event effect index,
    .scalar thread block (some .shared) event ∈ trace →
    event.memory = some effect → effect.kind = .load →
    index < n → effect.address = bytePointer index → effect.value = input[index]!

theorem readContract_append (n : Nat) (input : List Word) (left right : List (Event n)) :
    ReadContract n input (left ++ right) ↔ ReadContract n input left ∧ ReadContract n input right := by
  constructor
  · intro h
    exact ⟨fun t b e f i mem => h t b e f i (List.mem_append_left _ mem),
      fun t b e f i mem => h t b e f i (List.mem_append_right _ mem)⟩
  · rintro ⟨leftGood,rightGood⟩ t b e f i mem
    rcases List.mem_append.mp mem with before | after
    · exact leftGood t b e f i before
    · exact rightGood t b e f i after

def progress (n : Nat) (lane : Lane) : Nat := n - (lane.scalar.regs 0).toNat

def LaneInvariant (n : Nat) (input : List Word) (lane : Lane) : Prop :=
  match lane.block with
  | .initialize => (lane.scalar.pc = 2 ∨ lane.scalar.pc = 3) → lane.scalar.regs 1 = 0
  | .loop =>
      ((lane.scalar.pc = 0 ∨ lane.scalar.pc = 1 ∨ lane.scalar.pc = 2 ∨ lane.scalar.pc = 3 ∨
        lane.scalar.pc = 6 ∨ lane.scalar.pc = 7) → lane.scalar.regs 1 = total input (progress n lane)) ∧
      ((lane.scalar.pc = 4 ∨ lane.scalar.pc = 5) → lane.scalar.regs 1 = total input (progress n lane + 1)) ∧
      (lane.scalar.pc = 3 → lane.scalar.regs 2 = input[progress n lane]!)
  | .output => lane.scalar.regs 1 = total input n
  | _ => True

def Invariant (n : Nat) (input : List Word) (s : State n) : Prop :=
  ∀ thread, LaneInvariant n input (s.lanes thread)

theorem initial (input scratch : List Word) (seeds : Fin n → Seed) :
    Invariant n input (start input scratch seeds) := by
  intro thread
  trivial

theorem total_succ (input : List Word) (index : Nat) (inside : index < input.length) :
    total input (index+1) = total input index + input[index]! := by
  simp only [total,List.take_succ_eq_append_getElem inside,List.foldl_append,List.foldl_cons,List.foldl_nil]
  simp [inside]

/-- The candidate observation used by an actual successful shared-load step
is exactly the value stated by the trace's read contract. -/
theorem observed_value (cfg : Config n) (reads : Option Word) (s : State n)
    (thread : Fin n) (input : List Word) (index slot : Nat)
    (block : (s.lanes thread).block = .loop) (pc : (s.lanes thread).scalar.pc = 2)
    (live : (s.lanes thread).halted = false) (inside : index < n)
    (pointer : (s.lanes thread).scalar.addrs 0 = bytePointer index)
    (address : addressIndex s.shared ((s.lanes thread).scalar.addrs 0) = .ok slot)
    (contract : ReadContract n input (step cfg reads thread s).events) :
    reads.getD s.shared[slot]! = input[index]! := by
  let localState := {(s.lanes thread).scalar with memory := s.shared}
  let instruction := Instr.plain (.load 2 (.reg 0))
  let effect : MemoryEffect := ⟨.load,(s.lanes thread).scalar.addrs 0,reads.getD s.shared[slot]!⟩
  let event := occurrence localState instruction true (some effect)
  have member : .scalar thread .loop (some .shared) event ∈ (step cfg reads thread s).events := by
    simp [step,block,pc,live,program,dispatch,scalarStep,eval,Instr.plain,Guard.eval,
      Operand64.eval,address,event,localState,instruction,effect]
  exact contract thread .loop event effect index member rfl rfl inside pointer

/-- Minimal structural facts consumed by arithmetic; the reachable loop-control
invariant will discharge these independently of read values. -/
def Shape (n : Nat) (lane : Lane) : Prop :=
  (lane.block = .initialize → lane.scalar.pc = 3 → (lane.scalar.regs 0).toNat = n) ∧
  (lane.block = .loop →
    (lane.scalar.regs 0).toNat ≤ n ∧
    ((lane.scalar.pc = 2 ∨ lane.scalar.pc = 3 ∨ lane.scalar.pc = 4 ∨ lane.scalar.pc = 5) →
      0 < (lane.scalar.regs 0).toNat) ∧
    (lane.scalar.pc = 1 → lane.scalar.preds 0 = ((lane.scalar.regs 0).toNat == 0)) ∧
    (lane.scalar.pc = 7 → (lane.scalar.regs 0).toNat = 0) ∧
    (lane.scalar.pc = 2 → lane.scalar.addrs 0 = bytePointer (progress n lane)))

set_option maxHeartbeats 800000 in
private theorem selected_preserves (cfg : Config n) (reads : Option Word)
    (s : State n) (thread : Fin n) (input : List Word) (extent : n ≤ input.length)
    (shape : Shape n (s.lanes thread)) (data : LaneInvariant n input (s.lanes thread))
    (contract : ReadContract n input (step cfg reads thread s).events) :
    LaneInvariant n input ((step cfg reads thread s).state.lanes thread) := by
  by_cases stopped : (s.lanes thread).halted = true
  · simpa [step,stopped] using data
  have alive : (s.lanes thread).halted = false := Bool.eq_false_iff.mpr stopped
  have read_value (atLoop : (s.lanes thread).block = .loop)
      (atRead : (s.lanes thread).scalar.pc = 2) (slot : Nat)
      (address : addressIndex s.shared ((s.lanes thread).scalar.addrs 0) = .ok slot) :
      reads.getD s.shared[slot]! = input[progress n (s.lanes thread)]! := by
    have facts := shape.2 atLoop
    have positive := facts.2.1 (Or.inl atRead)
    exact observed_value cfg reads s thread input _ slot atLoop atRead alive
      (by dsimp [progress]; omega) (facts.2.2.2.2 atRead) address contract
  have decrement (atLoop : (s.lanes thread).block = .loop)
      (atDecrement : (s.lanes thread).scalar.pc = 5) :
      n - ((s.lanes thread).scalar.regs 0 - 1).toNat = progress n (s.lanes thread) + 1 := by
    have facts := shape.2 atLoop
    have positive := facts.2.1 (Or.inr (Or.inr (Or.inr atDecrement)))
    rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; change 1 ≤ ((s.lanes thread).scalar.regs 0).toNat; omega)]
    dsimp [progress]
    omega
  have sumStep (atLoop : (s.lanes thread).block = .loop)
      (atAdd : (s.lanes thread).scalar.pc = 3) :
      total input (progress n (s.lanes thread) + 1) =
        total input (progress n (s.lanes thread)) + input[progress n (s.lanes thread)]! := by
    apply total_succ
    have facts := shape.2 atLoop
    have positive := facts.2.1 (Or.inr (Or.inl atAdd))
    dsimp [progress]
    omega
  cases hb : (s.lanes thread).block
  all_goals rcases hp : (s.lanes thread).scalar.pc with _ | _ | _ | _ | _ | _ | _ | _ | k
  all_goals cases pred : (s.lanes thread).scalar.preds 0
  all_goals simp only [LaneInvariant,hb,hp] at data
  all_goals simp [step,alive,hb,hp,program,dispatch,scalarStep,eval,Instr.plain,Guard.eval,
    Operand32.eval,Operand64.eval,update,setLane,LaneInvariant,sharedStore,pred,progress]
  all_goals try {
    cases disposition : (Barrier.step (barrierConfig cfg) s.barrier
      (barrierRequest cfg s thread 0)).disposition <;> simp_all }
  all_goals cases address : addressIndex s.shared ((s.lanes thread).scalar.addrs 0)
  all_goals cases globalAddress : addressIndex s.global ((s.lanes thread).scalar.addrs 0)
  all_goals cases outputAddress : addressIndex s.global (bytePointer n)
  all_goals try simp_all [update,progress,Shape,BinOp.eval,total]

/-- Arithmetic is preserved by actual steps once independent control facts and
the observed-read contract have been supplied. -/
theorem step_preserves (cfg : Config n) (reads : Option Word) (s : State n)
    (thread : Fin n) (input : List Word) (extent : n ≤ input.length)
    (shape : ∀ lane, Shape n (s.lanes lane)) (data : Invariant n input s)
    (contract : ReadContract n input (step cfg reads thread s).events) :
    Invariant n input (step cfg reads thread s).state := by
  intro other
  by_cases released : (step cfg reads thread s).status = .released
  · rw [Data.release_lane_fields cfg reads s thread other released]
    trivial
  · by_cases same : other = thread
    · subst other; exact selected_preserves cfg reads s thread input extent (shape thread) (data thread) contract
    · rw [Data.step_other cfg reads s thread other same released]
      exact data other

private theorem fetched_global_store (block : Block) (pc : Nat) (i : Instr)
    (fetch : (program n block)[pc]? = some (.memory .global i))
    (store : Control.memoryKind i.op = some .store) :
    block = .output ∧ i = Instr.plain (.store (.imm (bytePointer n)) (.reg 1)) := by
  have member := List.mem_of_getElem? fetch
  cases block <;> simp [program] at member
  all_goals subst i
  · simp [Control.memoryKind,Instr.plain] at store
  · exact ⟨rfl,rfl⟩

private theorem scalar_output_value (reads : Option Word) (selected : Fin n) (s : State n)
    (thread : Fin n) (block : Block) (event : Occurrence) (effect : MemoryEffect)
    (member : .scalar thread block (some .global) event ∈
      (scalarStep reads selected (some .global)
        (Instr.plain (.store (.imm (bytePointer n)) (.reg 1))) s).events)
    (memory : event.memory = some effect) : effect.value = (s.lanes selected).scalar.regs 1 := by
  cases address : addressIndex s.global (bytePointer n) <;>
    simp [scalarStep,Instr.plain,eval,Guard.eval,Operand64.eval,address] at member
  obtain ⟨rfl,rfl,rfl⟩ := member
  simpa [occurrence,Operand32.eval] using
    (congrArg (fun x => x.map MemoryEffect.value) memory).symm

/-- The only actual global output store reads the proved accumulator. -/
theorem step_global_store_sum (cfg : Config n) (reads : Option Word) (selected : Fin n)
    (s : State n) (input : List Word) (thread : Fin n) (block : Block)
    (event : Occurrence) (effect : MemoryEffect) (data : Invariant n input s)
    (member : .scalar thread block (some .global) event ∈ (step cfg reads selected s).events)
    (memory : event.memory = some effect) (store : effect.kind = .store) :
    effect.value = total input n := by
  simp only [step] at member
  split at member
  · simp at member
  · split at member
    · simp at member
    · rename_i instruction fetch
      cases instruction with
      | localStep i =>
        have origin := Control.scalar_effect_origin reads selected none i s thread block (some .global) event effect member memory
        simp at origin
      | memory actualSpace i =>
        have origin := Control.scalar_effect_origin reads selected (some actualSpace) i s thread block (some .global) event effect member memory
        have spaceEq : actualSpace = .global := by simpa using origin.2.2.1.symm
        subst actualSpace
        obtain ⟨atOutput,rfl⟩ := fetched_global_store _ _ i fetch
          (by simpa [store] using origin.2.2.2.2.2.2)
        rw [scalar_output_value reads selected s thread block event effect member memory]
        have known := data selected
        simpa only [LaneInvariant,atOutput] using known
      | branch guard destination => simp [dispatch] at member
      | exit => simp [dispatch] at member
      | sync resource =>
        simp only [dispatch] at member
        split at member <;> simp only [List.mem_map] at member
        · simp at member
        all_goals obtain ⟨_,_,impossible⟩ := member; contradiction

/-- All arithmetic shape premises follow from the independent reachable-control
invariant; none are additional premises of initialized execution results. -/
theorem shape_of_loop (thread : Fin n) (lane : Lane) (inv : Loop.LaneInvariant thread lane) :
    Shape n lane := by
  constructor
  · intro block pc
    simp only [Loop.LaneInvariant,block] at inv
    exact inv.2.1 (by omega)
  · intro block
    simp only [Loop.LaneInvariant,block] at inv
    refine ⟨inv.2.2.1,?_,inv.2.2.2.2.1,inv.2.2.2.2.2.2,?_⟩
    · intro active
      exact inv.2.2.2.2.2.1 (by omega)
    · intro pc
      simpa [pc,Loop.progress,Loop.remaining,progress] using inv.2.2.2.1

theorem runWith_preserves (cfg : Config n) (reads : Nat → Option Word)
    (schedule : List (Fin n)) (s : State n) (input : List Word) (extent : n ≤ input.length)
    (control : Control.Invariant s) (data : Data.Invariant s) (loop : Loop.Invariant s)
    (sum : Invariant n input s) (contract : ReadContract n input (runWith cfg reads schedule s).trace) :
    Invariant n input (runWith cfg reads schedule s).state := by
  induction schedule generalizing reads s with
  | nil => exact sum
  | cons thread rest ih =>
    obtain ⟨first,later⟩ := (readContract_append _ _ _ _).mp contract
    exact ih _ _ (Control.step_preserves cfg (reads 0) thread s control)
      (Data.step_preserves cfg (reads 0) s thread control data)
      (Loop.step_preserves cfg (reads 0) s thread control data loop)
      (step_preserves cfg (reads 0) s thread input extent
        (fun t => shape_of_loop t _ (loop t)) sum first) later

theorem reachable (cfg : Config n) (reads : Nat → Option Word) (schedule : List (Fin n))
    (input scratch : List Word) (seeds : Fin n → Seed) (extent : n ≤ input.length)
    (contract : ReadContract n input (runWith cfg reads schedule (start input scratch seeds)).trace) :
    Invariant n input (runWith cfg reads schedule (start input scratch seeds)).state :=
  runWith_preserves cfg reads schedule _ input extent (Control.initial input scratch seeds)
    (Data.initial input scratch seeds) (Loop.initial input scratch seeds) (initial input scratch seeds) contract

theorem runWith_global_store_sum (cfg : Config n) (reads : Nat → Option Word)
    (schedule : List (Fin n)) (s : State n) (input : List Word) (extent : n ≤ input.length)
    (control : Control.Invariant s) (data : Data.Invariant s) (loop : Loop.Invariant s)
    (sum : Invariant n input s) (contract : ReadContract n input (runWith cfg reads schedule s).trace)
    (thread : Fin n) (block : Block) (event : Occurrence) (effect : MemoryEffect)
    (member : .scalar thread block (some .global) event ∈ (runWith cfg reads schedule s).trace)
    (memory : event.memory = some effect) (store : effect.kind = .store) :
    effect.value = total input n := by
  induction schedule generalizing reads s with
  | nil => simp [runWith] at member
  | cons selected rest ih =>
    obtain ⟨firstGood,laterGood⟩ := (readContract_append _ _ _ _).mp contract
    simp only [runWith,List.mem_append] at member
    rcases member with first | later
    · exact step_global_store_sum cfg (reads 0) selected s input thread block event effect sum first memory store
    · exact ih _ _ (Control.step_preserves cfg (reads 0) selected s control)
        (Data.step_preserves cfg (reads 0) s selected control data)
        (Loop.step_preserves cfg (reads 0) s selected control data loop)
        (step_preserves cfg (reads 0) s selected input extent
          (fun t => shape_of_loop t _ (loop t)) sum firstGood) laterGood later

/-- Every actual emitted output stores the complete modular sum. Memory-source
validity must discharge the separately named read contract. -/
theorem global_store_sum (cfg : Config n) (reads : Nat → Option Word) (schedule : List (Fin n))
    (input scratch : List Word) (seeds : Fin n → Seed) (extent : n ≤ input.length)
    (contract : ReadContract n input (runWith cfg reads schedule (start input scratch seeds)).trace)
    (thread : Fin n) (block : Block) (event : Occurrence) (effect : MemoryEffect)
    (member : .scalar thread block (some .global) event ∈
      (runWith cfg reads schedule (start input scratch seeds)).trace)
    (memory : event.memory = some effect) (store : effect.kind = .store) :
    effect.value = total input n :=
  runWith_global_store_sum cfg reads schedule _ input extent
    (Control.initial input scratch seeds) (Data.initial input scratch seeds)
    (Loop.initial input scratch seeds) (initial input scratch seeds) contract
    thread block event effect member memory store

end Ptx.Scalar.SharedReduction.Machine.ResultProof

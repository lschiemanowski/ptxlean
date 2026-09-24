import Ptx.SharedReductionData

namespace Ptx.Scalar.SharedReduction.Machine.Loop

def remaining (lane : Lane) : Nat := (lane.scalar.regs 0).toNat

def progress (n : Nat) (lane : Lane) : Nat := n - remaining lane

/-- Instruction boundaries expose the temporary one-slot pointer lead at PC5. -/
def LaneInvariant (thread : Fin n) (lane : Lane) : Prop :=
  match lane.block with
  | .choose => lane.scalar.pc = 1 → lane.scalar.preds 0 = (thread.val == 0)
  | .initialize => thread.val = 0 ∧
      (1 ≤ lane.scalar.pc → remaining lane = n) ∧
      (3 ≤ lane.scalar.pc → lane.scalar.addrs 0 = 0)
  | .loop => thread.val = 0 ∧ lane.scalar.pc ≤ 7 ∧ remaining lane ≤ n ∧
      lane.scalar.addrs 0 = bytePointer (progress n lane + if lane.scalar.pc = 5 then 1 else 0) ∧
      (lane.scalar.pc = 1 → lane.scalar.preds 0 = (remaining lane == 0)) ∧
      (2 ≤ lane.scalar.pc ∧ lane.scalar.pc ≤ 5 → 0 < remaining lane) ∧
      (lane.scalar.pc = 7 → remaining lane = 0)
  | .output => thread.val = 0 ∧ remaining lane = 0 ∧ lane.scalar.addrs 0 = bytePointer n
  | _ => True

def Invariant (s : State n) : Prop := ∀ thread, LaneInvariant thread (s.lanes thread)

theorem initial (input scratch : List Word) (seeds : Fin n → Seed) :
    Invariant (start input scratch seeds) := by intro thread; trivial

set_option maxHeartbeats 1600000 in
set_option maxRecDepth 4096 in
private theorem selected_preserves (cfg : Config n) (reads : Option Word)
    (s : State n) (thread : Fin n) (data : Data.LaneInvariant thread (s.lanes thread))
    (inv : LaneInvariant thread (s.lanes thread)) :
    LaneInvariant thread ((step cfg reads thread s).state.lanes thread) := by
  have nf : n < 2^32 := by have := cfg.noWrap; omega
  have tf : thread.val < 2^32 := by have := thread.isLt; omega
  have nbits : (BitVec.ofNat 32 n).toNat = n := by simp [BitVec.toNat_ofNat,Nat.mod_eq_of_lt nf]
  have tbits : (BitVec.ofNat 32 thread.val == (0 : Word)) = (thread.val == 0) := by
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq]
    constructor
    · intro h; have := congrArg BitVec.toNat h; simpa [BitVec.toNat_ofNat,Nat.mod_eq_of_lt tf] using this
    · intro h; simp [h]
  have zbits : ((s.lanes thread).scalar.regs 0 == (0 : Word)) =
      (((s.lanes thread).scalar.regs 0).toNat == 0) := by
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq]; exact ⟨fun h => by simp [h],fun h => BitVec.eq_of_toNat_eq (by simpa using h)⟩
  have increment (k : Nat) : bytePointer k + (4 : Address) = bytePointer (k+1) := by
    change BitVec.ofNat 64 (4*k) + BitVec.ofNat 64 4 = _
    rw [← BitVec.ofNat_add]; congr 1 <;> omega
  have decrement (positive : 0 < ((s.lanes thread).scalar.regs 0).toNat) :
      ((s.lanes thread).scalar.regs 0 - (1 : Word)).toNat =
        ((s.lanes thread).scalar.regs 0).toNat - 1 := by
    apply BitVec.toNat_sub_of_le
    change 1 ≤ ((s.lanes thread).scalar.regs 0).toNat
    omega
  by_cases stopped : (s.lanes thread).halted = true
  · simpa [step,stopped] using inv
  have alive : (s.lanes thread).halted = false := Bool.eq_false_iff.mpr stopped
  cases hb : (s.lanes thread).block
  all_goals rcases hp : (s.lanes thread).scalar.pc with _ | _ | _ | _ | _ | _ | _ | _ | k
  all_goals cases pred : (s.lanes thread).scalar.preds 0
  all_goals simp only [LaneInvariant,Data.LaneInvariant,hb,hp,remaining,progress] at inv data
  all_goals simp [step,alive,hb,hp,program,dispatch,scalarStep,eval,Instr.plain,Guard.eval,
    Operand32.eval,Operand64.eval,Compare.eval,BinOp.eval,update,setLane,LaneInvariant,remaining,progress,sharedStore,pred]
  all_goals try { cases disposition : (Barrier.step (barrierConfig cfg) s.barrier
      (barrierRequest cfg s thread 0)).disposition <;> simp_all }
  all_goals try { simp_all only [bytePointer,BitVec.ofNat_zero] }
  all_goals try omega
  all_goals first | (cases address : addressIndex s.shared ((s.lanes thread).scalar.addrs 0) <;> simp_all) | skip
  all_goals cases ga : addressIndex s.global ((s.lanes thread).scalar.addrs 0)
  all_goals cases oa : addressIndex s.global (bytePointer n)
  all_goals try simp_all [update]
  all_goals try { split <;> simp_all [LaneInvariant,remaining,progress] }

  all_goals try rfl
  all_goals try { constructor; omega; congr 1; omega }
  all_goals try omega

theorem step_preserves (cfg : Config n) (reads : Option Word) (s : State n) (thread : Fin n)
    (control : Control.Invariant s) (data : Data.Invariant s) (inv : Invariant s) :
    Invariant (step cfg reads thread s).state := by
  intro other
  by_cases released : (step cfg reads thread s).status = .released
  · rw [Data.release_lane_fields cfg reads s thread other released]
    simp [LaneInvariant]
  · by_cases same : other = thread
    · subst other; exact selected_preserves cfg reads s thread (data thread) (inv thread)
    · rw [Data.step_other cfg reads s thread other same released]; exact inv other

theorem runWith_preserves (cfg : Config n) (reads : Nat → Option Word)
    (schedule : List (Fin n)) (s : State n) (control : Control.Invariant s)
    (data : Data.Invariant s) (inv : Invariant s) :
    Invariant (runWith cfg reads schedule s).state := by
  induction schedule generalizing reads s with
  | nil => exact inv
  | cons thread rest ih =>
    exact ih _ _ (Control.step_preserves cfg (reads 0) thread s control)
      (Data.step_preserves cfg (reads 0) s thread control data)
      (step_preserves cfg (reads 0) s thread control data inv)

theorem reachable (cfg : Config n) (reads : Nat → Option Word) (schedule : List (Fin n))
    (input scratch : List Word) (seeds : Fin n → Seed) :
    Invariant (runWith cfg reads schedule (start input scratch seeds)).state :=
  runWith_preserves cfg reads schedule _ (Control.initial input scratch seeds)
    (Data.initial input scratch seeds) (initial input scratch seeds)

/-- The loop's actual load boundary has a positive remaining count. -/
theorem load_address (thread : Fin n) (lane : Lane) (inv : LaneInvariant thread lane)
    (block : lane.block = .loop) (pc : lane.scalar.pc = 2) :
    thread.val = 0 ∧ progress n lane < n ∧ lane.scalar.addrs 0 = bytePointer (progress n lane) := by
  simp only [LaneInvariant,block] at inv
  refine ⟨inv.1,?_,?_⟩
  · have := inv.2.2.2.2.2.1 (by omega)
    have := inv.2.2.1
    unfold progress
    omega
  · simpa [pc] using inv.2.2.2.1



private theorem fetched_load (block : Block) (pc : Nat) (i : Instr)
    (fetch : (program n block)[pc]? = some (.memory .shared i))
    (kind : Control.memoryKind i.op = some .load) :
    block = .loop ∧ pc = 2 ∧ i = .plain (.load 2 (.reg 0)) := by
  cases block <;> rcases pc with _ | _ | _ | _ | _ | _ | _ | _ | k
  all_goals simp [program] at fetch
  all_goals subst i
  all_goals simp_all [Control.memoryKind,sharedStore,Instr.plain]

private theorem scalar_load_address (reads : Option Word) (selected : Fin n)
    (s : State n) (thread : Fin n) (block : Block) (event : Occurrence) (effect : MemoryEffect)
    (member : .scalar thread block (some .shared) event ∈
      (scalarStep reads selected (some .shared) (.plain (.load 2 (.reg 0))) s).events)
    (memory : event.memory = some effect) : effect.address = (s.lanes selected).scalar.addrs 0 := by
  cases address : addressIndex s.shared ((s.lanes selected).scalar.addrs 0) with
  | error reason => simp [scalarStep,eval,Instr.plain,Guard.eval,Operand64.eval,address] at member
  | ok index =>
    simp only [scalarStep,eval,Instr.plain,Guard.eval,↓reduceIte,Operand64.eval,address] at member
    simp only [List.mem_singleton,Event.scalar.injEq] at member
    obtain ⟨rfl,rfl,_,rfl⟩ := member
    simpa [occurrence] using (congrArg (fun x => x.map MemoryEffect.address) memory).symm

/-- Every emitted shared load is the leader's actual valid next-slot load. -/
theorem step_shared_load_address (cfg : Config n) (reads : Option Word) (selected : Fin n)
    (s : State n) (thread : Fin n) (block : Block) (event : Occurrence) (effect : MemoryEffect)
    (inv : Invariant s)
    (member : .scalar thread block (some .shared) event ∈ (step cfg reads selected s).events)
    (memory : event.memory = some effect) (load : effect.kind = .load) :
    thread.val = 0 ∧ ∃ index : Fin n, effect.address = bytePointer index.val := by
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
        obtain ⟨atLoop,atLoad,rfl⟩ := fetched_load _ _ i fetch (by simpa [load] using origin.2.2.2.2.2.2)
        obtain ⟨leader,bound,address⟩ := load_address selected _ (inv selected) atLoop atLoad
        refine ⟨by simpa [origin.1] using leader,⟨progress n (s.lanes selected),bound⟩,?_⟩
        exact (scalar_load_address reads selected s thread block event effect member memory).trans address
      | branch guard destination => simp [dispatch] at member
      | exit => simp [dispatch] at member
      | sync resource =>
        simp only [dispatch] at member
        split at member <;> simp only [List.mem_map] at member
        · simp at member
        all_goals obtain ⟨_,_,impossible⟩ := member; contradiction

theorem runWith_shared_load_address (cfg : Config n) (reads : Nat → Option Word)
    (schedule : List (Fin n)) (s : State n) (thread : Fin n) (block : Block)
    (event : Occurrence) (effect : MemoryEffect) (control : Control.Invariant s)
    (data : Data.Invariant s) (inv : Invariant s)
    (member : .scalar thread block (some .shared) event ∈ (runWith cfg reads schedule s).trace)
    (memory : event.memory = some effect) (load : effect.kind = .load) :
    thread.val = 0 ∧ ∃ index : Fin n, effect.address = bytePointer index.val := by
  induction schedule generalizing reads s with
  | nil => simp [runWith] at member
  | cons selected rest ih =>
    simp only [runWith,List.mem_append] at member
    rcases member with first | later
    · exact step_shared_load_address cfg (reads 0) selected s thread block event effect inv first memory load
    · exact ih _ _ (Control.step_preserves cfg (reads 0) selected s control)
        (Data.step_preserves cfg (reads 0) s selected control data)
        (step_preserves cfg (reads 0) s selected control data inv) later

theorem reachable_shared_load_address (cfg : Config n) (reads : Nat → Option Word)
    (schedule : List (Fin n)) (input scratch : List Word) (seeds : Fin n → Seed)
    (thread : Fin n) (block : Block) (event : Occurrence) (effect : MemoryEffect)
    (member : .scalar thread block (some .shared) event ∈
      (runWith cfg reads schedule (start input scratch seeds)).trace)
    (memory : event.memory = some effect) (load : effect.kind = .load) :
    thread.val = 0 ∧ ∃ index : Fin n, effect.address = bytePointer index.val :=
  runWith_shared_load_address cfg reads schedule _ thread block event effect
    (Control.initial input scratch seeds) (Data.initial input scratch seeds)
    (initial input scratch seeds) member memory load



/-- Exit positions are facts about fetched exits, including leader election. -/
def TerminalLane (thread : Fin n) (lane : Lane) : Prop :=
  (lane.block = .choose → lane.scalar.pc = 2 → thread.val ≠ 0) ∧
  (lane.halted = true →
    (lane.block = .choose ∧ lane.scalar.pc = 2 ∧ thread.val ≠ 0) ∨
    (lane.block = .output ∧ lane.scalar.pc = 1))

def TerminalInvariant (s : State n) : Prop := ∀ thread, TerminalLane thread (s.lanes thread)

theorem terminal_initial (input scratch : List Word) (seeds : Fin n → Seed) :
    TerminalInvariant (start input scratch seeds) := by
  intro thread; simp [TerminalLane,start]

set_option maxHeartbeats 800000 in
private theorem terminal_selected (cfg : Config n) (reads : Option Word)
    (s : State n) (thread : Fin n) (inv : LaneInvariant thread (s.lanes thread))
    (terminal : TerminalLane thread (s.lanes thread)) :
    TerminalLane thread ((step cfg reads thread s).state.lanes thread) := by
  by_cases stopped : (s.lanes thread).halted = true
  · simpa [step,stopped] using terminal
  have alive : (s.lanes thread).halted = false := Bool.eq_false_iff.mpr stopped
  cases hb : (s.lanes thread).block
  all_goals rcases hp : (s.lanes thread).scalar.pc with _ | _ | _ | _ | _ | _ | _ | _ | k
  all_goals cases pred : (s.lanes thread).scalar.preds 0
  all_goals simp only [LaneInvariant,TerminalLane,hb,hp,alive,pred] at inv terminal
  all_goals simp [step,alive,hb,hp,program,dispatch,scalarStep,eval,Instr.plain,Guard.eval,
    Operand32.eval,Operand64.eval,Compare.eval,BinOp.eval,update,setLane,TerminalLane,sharedStore,pred]
  all_goals try { cases disposition : (Barrier.step (barrierConfig cfg) s.barrier
      (barrierRequest cfg s thread 0)).disposition <;> simp_all }
  all_goals first | (cases address : addressIndex s.shared ((s.lanes thread).scalar.addrs 0) <;> simp_all) | skip
  all_goals cases ga : addressIndex s.global ((s.lanes thread).scalar.addrs 0)
  all_goals cases oa : addressIndex s.global (bytePointer n)
  all_goals simp_all

theorem terminal_step (cfg : Config n) (reads : Option Word) (s : State n) (thread : Fin n)
    (control : Control.Invariant s) (inv : Invariant s) (terminal : TerminalInvariant s) :
    TerminalInvariant (step cfg reads thread s).state := by
  intro other
  by_cases released : (step cfg reads thread s).status = .released
  · rw [Data.release_lane_fields cfg reads s thread other released]
    have atSite := Control.release_all_at_barrier cfg reads s thread control released other
    simp [TerminalLane,atSite.2.2]
  · by_cases same : other = thread
    · subst other; exact terminal_selected cfg reads s thread (inv thread) (terminal thread)
    · rw [Data.step_other cfg reads s thread other same released]; exact terminal other

theorem terminal_runWith (cfg : Config n) (reads : Nat → Option Word)
    (schedule : List (Fin n)) (s : State n) (control : Control.Invariant s)
    (data : Data.Invariant s) (inv : Invariant s) (terminal : TerminalInvariant s) :
    TerminalInvariant (runWith cfg reads schedule s).state := by
  induction schedule generalizing reads s with
  | nil => exact terminal
  | cons thread rest ih =>
    exact ih _ _ (Control.step_preserves cfg (reads 0) thread s control)
      (Data.step_preserves cfg (reads 0) s thread control data)
      (step_preserves cfg (reads 0) s thread control data inv)
      (terminal_step cfg (reads 0) s thread control inv terminal)

theorem terminal_reachable (cfg : Config n) (reads : Nat → Option Word)
    (schedule : List (Fin n)) (input scratch : List Word) (seeds : Fin n → Seed) :
    TerminalInvariant (runWith cfg reads schedule (start input scratch seeds)).state :=
  terminal_runWith cfg reads schedule _ (Control.initial input scratch seeds)
    (Data.initial input scratch seeds) (initial input scratch seeds)
    (terminal_initial input scratch seeds)

theorem halted_leader (cfg : Config n) (reads : Nat → Option Word)
    (schedule : List (Fin n)) (input scratch : List Word) (seeds : Fin n → Seed)
    (leader : Fin n) (zero : leader.val = 0)
    (halted : ((runWith cfg reads schedule (start input scratch seeds)).state.lanes leader).halted = true) :
    ((runWith cfg reads schedule (start input scratch seeds)).state.lanes leader).block = .output ∧
    ((runWith cfg reads schedule (start input scratch seeds)).state.lanes leader).scalar.pc = 1 := by
  have h := (terminal_reachable cfg reads schedule input scratch seeds leader).2 halted
  rcases h with ⟨_,_,impossible⟩ | output
  · exact False.elim (impossible zero)
  · exact output

end Ptx.Scalar.SharedReduction.Machine.Loop

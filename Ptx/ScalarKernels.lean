import Ptx.Scalar

/-! Concrete instruction-level integer kernels. Results concern the explicit
owned sequential arena discipline, not a complete weak-memory PTX model. -/
namespace Ptx.Scalar.Kernels

/-- A lane reads two input words and writes their modular u32 sum. -/
def addLane : List Instr := [
  .plain (.load 0 (.imm 0)),
  .plain (.load 1 (.imm 4)),
  .plain (.bin32 .add 2 (.reg 0) (.reg 1)),
  .plain (.store (.imm 8) (.reg 2)),
  .plain .exit]

/-- All initial registers are explicit inputs; only the three designated registers change. -/
def laneStart (x y old : Word) (tail : List Word)
    (registers : Nat → Word) (addresses : Nat → Address) (predicates : Nat → Bool) : State :=
  ⟨0, registers, addresses, predicates, x :: y :: old :: tail⟩

theorem add_lane_result (x y old : Word) (tail : List Word) (registers addresses predicates) :
    let result := run 5 addLane (laneStart x y old tail registers addresses predicates)
    result.status = .halted ∧ result.state.memory = x :: y :: (x + y) :: tail ∧
    result.state.regs 2 = x + y := by
  simp [run, runWith, stepWith, eval, Guard.eval, Instr.plain, addLane,
    laneStart, addressIndex, Operand64.eval, Operand32.eval, BinOp.eval, update]

/-- Observable lane-wise composition over separately owned three-word views.
The caller supplies the disjoint-view interpretation; this is no GPU scheduler theorem. -/
theorem elementwise_add (n : Nat) (left right old : Fin n → Word)
    (registers : Fin n → Nat → Word) (addresses : Fin n → Nat → Address)
    (predicates : Fin n → Nat → Bool) :
    ∀ lane,
      let result := run 5 addLane (laneStart (left lane) (right lane) (old lane) []
        (registers lane) (addresses lane) (predicates lane))
      result.status = .halted ∧
        result.state.memory = [left lane, right lane, left lane + right lane] := by
  intro lane
  obtain ⟨hh, hm, _⟩ := add_lane_result (left lane) (right lane) (old lane) []
    (registers lane) (addresses lane) (predicates lane)
  exact ⟨hh, hm⟩

/-- r0=count, r1=accumulator, rd0=byte cursor. Each iteration performs a real
load and advances the cursor; zero count takes the exit branch without a load. -/
def sumLoop : List Instr := [
  .plain (.setp .eq 0 (.reg 0) (.imm 0)),
  ⟨.pred 0 true, .bra 7⟩,
  .plain (.load 2 (.reg 0)),
  .plain (.bin32 .add 1 (.reg 1) (.reg 2)),
  .plain (.add64 0 (.reg 0) (.imm 4)),
  .plain (.bin32 .sub 0 (.reg 0) (.imm 1)),
  .plain (.bra 0),
  .plain .exit]

/-- Projection used for functional reasoning; full traces remain in `run`. -/
def outcome (fuel : Nat) (program : List Instr) (s : State) : Stop × State :=
  let result := run fuel program s
  (result.status, result.state)

def loopNext (s : State) (value : Word) : State :=
  { s with
    pc := 0
    regs := update (update (update s.regs 2 value) 1 (s.regs 1 + value)) 0 (s.regs 0 - 1)
    addrs := update s.addrs 0 (s.addrs 0 + 4)
    preds := update s.preds 0 false}

theorem loop_zero (s : State) (pc : s.pc = 0) (count : s.regs 0 = 0) :
    (outcome 3 sumLoop s).1 = .halted ∧
    (outcome 3 sumLoop s).2.memory = s.memory ∧
    (outcome 3 sumLoop s).2.regs 1 = s.regs 1 := by
  simp [outcome, run, runWith, stepWith, eval, Guard.eval, Instr.plain, sumLoop,
    pc, count, Compare.eval, Operand32.eval, update]

theorem loop_advance (s : State) (pc : s.pc = 0) (count : s.regs 0 ≠ 0)
    (address : addressIndex s.memory (s.addrs 0) = .ok index) (fuel : Nat) :
    outcome (fuel + 7) sumLoop s =
      outcome fuel sumLoop (loopNext s s.memory[index]!) := by
  change s.regs 0 ≠ 0#32 at count
  have hc : (s.regs 0 == 0#32) = false := by simp [count]
  simp [outcome, run, runWith, stepWith, eval, Guard.eval, Instr.plain, sumLoop,
    pc, hc, Compare.eval, Operand32.eval, Operand64.eval, BinOp.eval,
    address, loopNext, update]

/-- Pure modular-u32 reference computation over a memory slice. -/
def sliceSum (memory : List Word) (start count : Nat) (initial : Word) : Word :=
  ((memory.drop start).take count).foldl (fun total word => total + word) initial

/-- A parametric termination and functional-correctness theorem for the actual
branching load/accumulate loop. The bounds prevent counter and pointer wrap. -/
theorem sum_loop_correct (count : Nat) (s : State) (start : Nat)
    (pc : s.pc = 0) (counter : s.regs 0 = BitVec.ofNat 32 count)
    (pointer : s.addrs 0 = BitVec.ofNat 64 (4 * start))
    (extent : start + count ≤ s.memory.length)
    (countFits : count < 2^32) (addressFits : 4 * (start + count) < 2^64) :
    let final := outcome (7 * count + 3) sumLoop s
    final.1 = .halted ∧ final.2.memory = s.memory ∧
      final.2.regs 1 = sliceSum s.memory start count (s.regs 1) := by
  induction count generalizing s start with
  | zero =>
    simpa [sliceSum] using loop_zero s pc counter
  | succ count ih =>
    have inside : start < s.memory.length := by omega
    have addressNat : (s.addrs 0).toNat = 4 * start := by
      rw [pointer]
      simp only [BitVec.toNat_ofNat]
      exact Nat.mod_eq_of_lt (by omega)
    have indexOK : addressIndex s.memory (s.addrs 0) = .ok start := by
      simp [addressIndex, addressNat, inside]
    have nonzero : s.regs 0 ≠ 0 := by
      intro zero
      have h := congrArg BitVec.toNat zero
      rw [counter] at h
      simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt countFits] at h
      have : (0 : Word).toNat = 0 := rfl
      rw [this] at h
      omega
    let next := loopNext s s.memory[start]!
    have nextCounter : next.regs 0 = BitVec.ofNat 32 count := by
      simp only [next, loopNext, update_same, counter]
      change BitVec.ofNat 32 (count + 1) - BitVec.ofNat 32 1 = BitVec.ofNat 32 count
      rw [BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) (by omega)]
      simp
    have nextPointer : next.addrs 0 = BitVec.ofNat 64 (4 * (start + 1)) := by
      simp only [next, loopNext, update_same, pointer]
      change BitVec.ofNat 64 (4 * start) + BitVec.ofNat 64 4 = _
      rw [← BitVec.ofNat_add]
      congr 1
    have inductionResult := ih next (start + 1) rfl nextCounter nextPointer
      (by change start + 1 + count ≤ s.memory.length; omega) (by omega) (by omega)
    have budget : 7 * (count + 1) + 3 = (7 * count + 3) + 7 := by omega
    change (outcome (7 * (count + 1) + 3) sumLoop s).1 = .halted ∧ _
    rw [budget, loop_advance s pc nonzero indexOK]
    refine ⟨inductionResult.1, inductionResult.2.1, ?_⟩
    rw [inductionResult.2.2]
    simp only [sliceSum, next, loopNext]
    rw [List.drop_eq_getElem_cons inside]
    simp [update, inside, -List.getElem_cons_drop]

/-- A completed instruction-level derivation, with its result and preserved tail. -/
theorem add_lane_exists (x y old : Word) (tail : List Word) (registers addresses predicates) :
    ∃ result, Runs addLane (fun _ => none)
      (laneStart x y old tail registers addresses predicates) result ∧
      result.status = .halted ∧ result.state.memory = x :: y :: (x + y) :: tail := by
  refine ⟨run 5 addLane (laneStart x y old tail registers addresses predicates),
    run_sound _ _ _, ?_⟩
  exact ⟨(add_lane_result _ _ _ _ _ _ _).1, (add_lane_result _ _ _ _ _ _ _).2.1⟩

/-- Existence means a halted derivation, not merely a fuel-exhausted prefix. -/
theorem sum_loop_exists (count : Nat) (s : State) (start : Nat)
    (pc : s.pc = 0) (counter : s.regs 0 = BitVec.ofNat 32 count)
    (pointer : s.addrs 0 = BitVec.ofNat 64 (4 * start))
    (extent : start + count ≤ s.memory.length)
    (countFits : count < 2^32) (addressFits : 4 * (start + count) < 2^64) :
    ∃ result, Runs sumLoop (fun _ => none) s result ∧ result.status = .halted ∧
      result.state.memory = s.memory ∧
      result.state.regs 1 = sliceSum s.memory start count (s.regs 1) := by
  exact ⟨run (7 * count + 3) sumLoop s, run_sound _ _ _,
    sum_loop_correct count s start pc counter pointer extent countFits addressFits⟩

/-- Larger budgets give exactly the same completed run, including its trace. -/
theorem sum_loop_extra_fuel (count extra : Nat) (s : State) (start : Nat)
    (pc : s.pc = 0) (counter : s.regs 0 = BitVec.ofNat 32 count)
    (pointer : s.addrs 0 = BitVec.ofNat 64 (4 * start))
    (extent : start + count ≤ s.memory.length)
    (countFits : count < 2^32) (addressFits : 4 * (start + count) < 2^64) :
    run ((7 * count + 3) + extra) sumLoop s = run (7 * count + 3) sumLoop s := by
  have halted := (sum_loop_correct count s start pc counter pointer extent countFits addressFits).1
  change (run (7 * count + 3) sumLoop s).status = .halted at halted
  rw [run_add]
  simp only [resume, halted, reduceCtorEq, ↓reduceIte]

/-- All accesses in the completed loop have full four-byte bounds and alignment. -/
theorem sum_loop_memory_safe (count : Nat) (s : State)
    (event : Occurrence) (member : event ∈ (run (7 * count + 3) sumLoop s).trace)
    (effect : MemoryEffect) (memory : event.memory = some effect) :
    effect.address.toNat % 4 = 0 ∧ effect.address.toNat + 4 ≤ 4 * s.memory.length :=
  validAddress_bytes (run_trace_safe _ _ _ event member effect memory)

end Ptx.Scalar.Kernels

import PtxBinary32.Mixed
import PtxBinary32Error
import Ptx.AffineMemory

/-! A concrete isolated arena program with actual load/multiply/add/store/exit
steps. Numerical theorems concern all completed runs of this restricted semantics;
they do not identify it with general concurrent PTX admission. -/
namespace Ptx.Scalar.Affine

open Mixed

def load (index : Nat) : Scalar.Instr := .plain (.load index (.reg index))
def multiply : Scalar.Binary32.Instr := ⟨.always, .mul, 3, .reg 0, .reg 1⟩
def addition : Scalar.Binary32.Instr := ⟨.always, .add, 4, .reg 3, .reg 2⟩
def store : Scalar.Instr := .plain (.store (.reg 3) (.reg 4))
def exit : Scalar.Instr := .plain .exit

def program : List Mixed.Instr :=
  [.scalar (load 0), .scalar (load 1), .scalar (load 2),
    .binary32 multiply, .binary32 addition, .scalar store, .scalar exit]

/-- Addresses can alias; initialization is the supplied initial arena snapshot. -/
def Initial (s : State) : Prop :=
  s.pc = 0 ∧ ∀ i : Fin 4, ValidAddress s.memory (s.addrs i.val)

def input (s : State) (i : Nat) : Word := s.memory[(s.addrs i).toNat / 4]!
def outputIndex (s : State) : Nat := (s.addrs 3).toNat / 4

def afterLeft (s : State) : State :=
  {s with pc := 1, regs := update s.regs 0 (input s 0)}
def afterRight (s : State) : State :=
  {afterLeft s with pc := 2, regs := update (afterLeft s).regs 1 (input s 1)}
def afterBias (s : State) : State :=
  {afterRight s with pc := 3, regs := update (afterRight s).regs 2 (input s 2)}
def afterMultiply (s : State) (mid : Word) : State :=
  {afterBias s with pc := 4, regs := update (afterBias s).regs 3 mid}
def afterAdd (s : State) (mid out : Word) : State :=
  {afterMultiply s mid with pc := 5, regs := update (afterMultiply s mid).regs 4 out}
def finish (s : State) (mid out : Word) : State :=
  {afterAdd s mid out with pc := 6, memory := s.memory.set (outputIndex s) out}

def loadEvent (s : State) (i : Nat) : Mixed.Event :=
  .scalar (Scalar.occurrence {s with pc := i} (load i) true
    (some ⟨.load, s.addrs i, input s i⟩))
def trace (s : State) (mid out : Word) : List Mixed.Event :=
  [loadEvent s 0, loadEvent s 1, loadEvent s 2,
    .binary32 (Scalar.Binary32.occurrence (afterBias s) multiply true),
    .binary32 (Scalar.Binary32.occurrence (afterMultiply s mid) addition true),
    .scalar (Scalar.occurrence (afterAdd s mid out) store true
      (some ⟨.store, s.addrs 3, out⟩)),
    .scalar (Scalar.occurrence (finish s mid out) exit true)]

private theorem index_ok (h : ValidAddress memory address) :
    addressIndex memory address = .ok (address.toNat / 4) :=
  addressIndex_ok_iff.mpr ⟨h, rfl⟩

private theorem load_left (h : Initial s) : Scalar.eval none (load 0) s =
    .next (afterLeft s) (Scalar.occurrence s (load 0) true (some ⟨.load, s.addrs 0, input s 0⟩)) := by
  have hi : addressIndex s.memory (s.addrs 0) = .ok ((s.addrs 0).toNat / 4) := index_ok (h.2 0)
  simp [load, Scalar.eval, Instr.plain, Guard.eval, Operand64.eval,
    hi, input, afterLeft, Scalar.occurrence, h.1]

private theorem load_right (h : Initial s) : Scalar.eval none (load 1) (afterLeft s) =
    .next (afterRight s) (Scalar.occurrence (afterLeft s) (load 1) true
      (some ⟨.load, s.addrs 1, input s 1⟩)) := by
  have hi : addressIndex s.memory (s.addrs 1) = .ok ((s.addrs 1).toNat / 4) := index_ok (h.2 1)
  simp [load, Scalar.eval, Scalar.Instr.plain, Guard.eval, Operand64.eval,
    afterLeft, afterRight, hi, input]

private theorem load_bias (h : Initial s) : Scalar.eval none (load 2) (afterRight s) =
    .next (afterBias s) (Scalar.occurrence (afterRight s) (load 2) true
      (some ⟨.load, s.addrs 2, input s 2⟩)) := by
  have hi : addressIndex s.memory (s.addrs 2) = .ok ((s.addrs 2).toNat / 4) := index_ok (h.2 2)
  simp [load, Scalar.eval, Scalar.Instr.plain, Guard.eval, Operand64.eval,
    afterLeft, afterRight, afterBias, hi, input]

private theorem store_output (h : Initial s) (mid out : Word) :
    Scalar.eval none store (afterAdd s mid out) = .next (finish s mid out)
      (Scalar.occurrence (afterAdd s mid out) store true (some ⟨.store, s.addrs 3, out⟩)) := by
  have hi : addressIndex s.memory (s.addrs 3) = .ok ((s.addrs 3).toNat / 4) := index_ok (h.2 3)
  simp [store, Scalar.eval, Scalar.Instr.plain, Guard.eval, Operand64.eval, Operand32.eval,
    afterLeft, afterRight, afterBias, afterMultiply, afterAdd, finish, outputIndex,
    hi]

/-- Every terminal run is the actual seven-step computation, with unrestricted
valid-address aliases and every numerical result in the original envelope. -/
theorem run_iff (s : State) (target : Ptx.Target) (h : Initial s)
    (eligible : Mixed.Eligible target) (final : State) (status : Scalar.Stop)
    (events : List Mixed.Event) :
    Mixed.Run target program s final status events ↔
      ∃ mid out, Ptx.Binary32.Error.AffineResults (input s 0) (input s 1) (input s 2) mid out ∧
        final = finish s mid out ∧ status = .halted ∧ events = trace s mid out := by
  rw [Mixed.Run.scalar_next_iff (program := program) eligible (by simp [program, h.1]) (load_left h)]
  simp_rw [Mixed.Run.scalar_next_iff (program := program) eligible
    (by simp [program, afterLeft]) (load_right h)]
  simp_rw [Mixed.Run.scalar_next_iff (program := program) eligible
    (by simp [program, afterRight]) (load_bias h)]
  simp_rw [Mixed.Run.binary32_iff (program := program) eligible
    (by simp [program, afterBias]) (show multiply.guard.eval (afterBias s) = true from rfl)]
  change (∃ rest, (∃ rest_1, (∃ rest_2,
    (∃ mid, Ptx.Binary32.Results .mul (input s 0) (input s 1) mid ∧ ∃ rest_3,
      Mixed.Run target program (afterMultiply s mid) final status rest_3 ∧
      rest_2 = .binary32 (Scalar.Binary32.occurrence (afterBias s) multiply true) :: rest_3) ∧
    rest_1 = _ :: rest_2) ∧ rest = _ :: rest_1) ∧ events = _ :: rest) ↔ _
  simp_rw [Mixed.Run.binary32_iff (program := program) (s := afterMultiply s _) eligible
    (by simp [program, afterMultiply]) (show addition.guard.eval _ = true from rfl)]
  change (∃ rest, (∃ rest_1, (∃ rest_2,
    (∃ mid, Ptx.Binary32.Results .mul (input s 0) (input s 1) mid ∧ ∃ rest_3,
      (∃ out, Ptx.Binary32.Results .add mid (input s 2) out ∧ ∃ rest_4,
        Mixed.Run target program (afterAdd s mid out) final status rest_4 ∧
        rest_3 = .binary32 (Scalar.Binary32.occurrence (afterMultiply s mid) addition true) :: rest_4) ∧
      rest_2 = _ :: rest_3) ∧ rest_1 = _ :: rest_2) ∧ rest = _ :: rest_1) ∧ events = _ :: rest) ↔ _
  simp_rw [Mixed.Run.scalar_next_iff (program := program) (s := afterAdd s _ _) eligible (by simp [program, afterAdd]) (store_output h _ _)]
  simp_rw [Mixed.Run.scalar_halted_iff (program := program) (s := finish s _ _) eligible (by simp [program, finish])
    (show Scalar.eval none exit (finish s _ _) = .halted (finish s _ _)
      (Scalar.occurrence (finish s _ _) exit true) from rfl)]
  simp only [Ptx.Binary32.Error.AffineResults, trace, loadEvent]
  constructor
  · rintro ⟨r0, ⟨r1, ⟨r2, ⟨mid, hm, r3, ⟨out, ho, r4, ⟨r5, ⟨hf, hs, ht⟩, h4⟩, h3⟩, h2⟩, h1⟩, h0⟩, he⟩
    refine ⟨mid, out, ⟨hm, ho⟩, hf, hs, ?_⟩
    subst r5 r4 r3 r2 r1 r0
    simpa [afterLeft, afterRight, Scalar.occurrence, h.1] using he
  · rintro ⟨mid, out, ⟨hm, ho⟩, rfl, rfl, rfl⟩
    refine ⟨_, ⟨_, ⟨_, ⟨mid, hm, _, ⟨out, ho, _, ⟨_, ⟨rfl, rfl, rfl⟩, rfl⟩, rfl⟩, rfl⟩, rfl⟩, rfl⟩, ?_⟩
    simp [afterLeft, afterRight, Scalar.occurrence, h.1]

/-- A reference result at each actual arithmetic step supplies a finite run,
without assuming finite inputs or assuming the desired final memory. -/
theorem run_exists (s : State) (target : Ptx.Target) (h : Initial s)
    (eligible : Mixed.Eligible target) :
    ∃ final events, Mixed.Run target program s final .halted events := by
  obtain ⟨mid, hm⟩ := Ptx.Binary32.results_exists .mul (input s 0) (input s 1)
  obtain ⟨out, ho⟩ := Ptx.Binary32.results_exists .add mid (input s 2)
  exact ⟨finish s mid out, trace s mid out,
    (run_iff s target h eligible _ _ _).2 ⟨mid, out, ⟨hm, ho⟩, rfl, rfl, rfl⟩⟩

theorem trace_length (s : State) (mid out : Word) : (trace s mid out).length = 7 := rfl

theorem trace_positions (s : State) (mid out : Word) :
    (trace s mid out).map Mixed.Event.pc = [0, 1, 2, 3, 4, 5, 6] := rfl

theorem trace_instructions (s : State) (mid out : Word) :
    (trace s mid out).map Mixed.Event.instruction = program := rfl

theorem trace_memory (s : State) (mid out : Word) :
    (trace s mid out).filterMap Mixed.Event.memory =
      [⟨.load, s.addrs 0, input s 0⟩, ⟨.load, s.addrs 1, input s 1⟩,
       ⟨.load, s.addrs 2, input s 2⟩, ⟨.store, s.addrs 3, out⟩] := rfl

theorem finish_frame (s : State) (mid out : Word) :
    (finish s mid out).pc = 6 ∧ (finish s mid out).addrs = s.addrs ∧
    (finish s mid out).preds = s.preds ∧
    (finish s mid out).memory = s.memory.set (outputIndex s) out := ⟨rfl, rfl, rfl, rfl⟩

theorem finish_registers (s : State) (mid out : Word) :
    (finish s mid out).regs 0 = input s 0 ∧
    (finish s mid out).regs 1 = input s 1 ∧
    (finish s mid out).regs 2 = input s 2 ∧
    (finish s mid out).regs 3 = mid ∧ (finish s mid out).regs 4 = out := by
  simp [finish, afterAdd, afterMultiply, afterBias, afterRight, afterLeft, update]

theorem finish_other_register (s : State) (mid out : Word) (index : Nat)
    (other : 5 ≤ index) : (finish s mid out).regs index = s.regs index := by
  have h0 : index ≠ 0 := by omega
  have h1 : index ≠ 1 := by omega
  have h2 : index ≠ 2 := by omega
  have h3 : index ≠ 3 := by omega
  have h4 : index ≠ 4 := by omega
  simp [finish, afterAdd, afterMultiply, afterBias, afterRight, afterLeft,
    update, h0, h1, h2, h3, h4]

theorem finish_output (s : State) (mid out : Word) (h : Initial s) :
    (finish s mid out).memory[outputIndex s]? = some out := by
  have bound : outputIndex s < s.memory.length := (h.2 3).2
  simp [finish, bound]

theorem finish_other_memory (s : State) (mid out : Word) (index : Nat)
    (other : index ≠ outputIndex s) :
    (finish s mid out).memory[index]? = s.memory[index]? := by
  exact List.getElem?_set_ne (Ne.symm other)

/-- All terminal runs from the stated layout halt, and record all seven events.
This does not turn a shorter advancing prefix into a completed run. -/
theorem run_completed (s : State) (target : Ptx.Target) (h : Initial s)
    (eligible : Mixed.Eligible target) (run : Mixed.Run target program s final status events) :
    status = .halted ∧ final.pc = 6 ∧ events.length = 7 ∧
      events.map Mixed.Event.pc = [0, 1, 2, 3, 4, 5, 6] := by
  obtain ⟨mid, out, _, rfl, rfl, rfl⟩ := (run_iff s target h eligible _ _ _).1 run
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- The absolute error concerns the actual final memory word. The only numerical
premises constrain initial finite input values, input deviations and ranges. -/
theorem stored_error (s : State) (target : Ptx.Target) (h : Initial s)
    (eligible : Mixed.Eligible target) (run : Mixed.Run target program s final status events)
    (xh yh bh x y b ex ey eb : ℝ)
    (leftReal : Ptx.Binary32.finiteReal (input s 0) = some xh)
    (rightReal : Ptx.Binary32.finiteReal (input s 1) = some yh)
    (biasReal : Ptx.Binary32.finiteReal (input s 2) = some bh)
    (multiplyRange : |xh*yh| ≤ Ptx.Binary32.Bounds.maxFinite)
    (additionRange : |xh*yh| + TorchLean.Floats.eps32 (xh*yh) + |bh| ≤ Ptx.Binary32.Bounds.maxFinite)
    (leftError : |xh-x| ≤ ex) (rightError : |yh-y| ≤ ey) (biasError : |bh-b| ≤ eb) :
    status = .halted ∧ ∃ out z,
      final.memory[outputIndex s]? = some out ∧ Ptx.Binary32.isFinite out = true ∧
      Ptx.Binary32.finiteReal out = some z ∧
      |z-(x*y+b)| ≤ Ptx.Binary32.Error.affineBudget xh yh bh x y ex ey eb := by
  obtain ⟨mid, out, allowed, rfl, rfl, rfl⟩ := (run_iff s target h eligible _ _ _).1 run
  obtain ⟨_, finite, z, real, error⟩ := Ptx.Binary32.Error.affine_results
    (input s 0) (input s 1) (input s 2) mid out xh yh bh x y b ex ey eb
    leftReal rightReal biasReal multiplyRange additionRange leftError rightError biasError allowed
  exact ⟨rfl, out, z, finish_output s mid out h, finite, real, error⟩

private theorem load_advances (h : Scalar.eval none (load index) s = .next next event) :
    next.pc = s.pc + 1 := by
  simp only [load, Scalar.Instr.plain, Scalar.eval, Guard.eval, ↓reduceIte, Operand64.eval] at h
  split at h
  · contradiction
  · cases h; rfl

private theorem store_advances (h : Scalar.eval none store s = .next next event) :
    next.pc = s.pc + 1 := by
  simp only [store, Scalar.Instr.plain, Scalar.eval, Guard.eval, ↓reduceIte, Operand64.eval] at h
  split at h
  · contradiction
  · cases h; rfl

/-- Advancing control cannot loop or pass the explicit exit, irrespective of FP
result choices. The premise concerns the current PC, not a desired output. -/
theorem advance_pc (step : Mixed.Advances target program s event next) (bounded : s.pc ≤ 6) :
    next.pc = s.pc + 1 ∧ s.pc < 6 := by
  rcases step with ⟨_, step⟩
  have pcs : s.pc = 0 ∨ s.pc = 1 ∨ s.pc = 2 ∨ s.pc = 3 ∨ s.pc = 4 ∨ s.pc = 5 ∨ s.pc = 6 := by omega
  rcases pcs with hp | hp | hp | hp | hp | hp | hp
  · simp only [program, hp, List.getElem?_cons_succ, List.getElem?_cons_zero] at step
    obtain ⟨ev, hs, _⟩ := Mixed.scalar_next_iff.mp step
    exact ⟨load_advances hs, by omega⟩
  · simp only [program, hp, List.getElem?_cons_succ, List.getElem?_cons_zero] at step
    obtain ⟨ev, hs, _⟩ := Mixed.scalar_next_iff.mp step
    exact ⟨load_advances hs, by omega⟩
  · simp only [program, hp, List.getElem?_cons_succ, List.getElem?_cons_zero] at step
    obtain ⟨ev, hs, _⟩ := Mixed.scalar_next_iff.mp step
    exact ⟨load_advances hs, by omega⟩
  · simp only [program, hp, List.getElem?_cons_succ, List.getElem?_cons_zero] at step
    obtain ⟨ns, ev, he, eq⟩ := Mixed.eval_binary32_iff.mp step
    cases eq
    exact ⟨(Scalar.Binary32.eval_frame _ _ _ _ he).1, by omega⟩
  · simp only [program, hp, List.getElem?_cons_succ, List.getElem?_cons_zero] at step
    obtain ⟨ns, ev, he, eq⟩ := Mixed.eval_binary32_iff.mp step
    cases eq
    exact ⟨(Scalar.Binary32.eval_frame _ _ _ _ he).1, by omega⟩
  · simp only [program, hp, List.getElem?_cons_succ, List.getElem?_cons_zero] at step
    obtain ⟨ev, hs, _⟩ := Mixed.scalar_next_iff.mp step
    exact ⟨store_advances hs, by omega⟩
  · simp only [program, hp, List.getElem?_cons_succ, List.getElem?_cons_zero] at step
    obtain ⟨ev, hs, _⟩ := Mixed.scalar_next_iff.mp step
    simp [exit, Scalar.Instr.plain, Scalar.eval, Guard.eval] at hs

theorem path_control (path : Mixed.Path (Mixed.Advances target program) s events final)
    (bounded : s.pc ≤ 6) : final.pc = s.pc + events.length ∧ final.pc ≤ 6 := by
  induction path with
  | nil => simp [bounded]
  | cons step _ ih =>
    obtain ⟨advanced, prior⟩ := advance_pc step bounded
    obtain ⟨endPC, endBound⟩ := ih (by omega)
    exact ⟨by simp only [List.length_cons]; omega, endBound⟩

theorem path_bound (path : Mixed.Path (Mixed.Advances target program) s events final)
    (initialPC : s.pc = 0) : events.length ≤ 6 := by
  obtain ⟨endPC, endBound⟩ := path_control path (by omega)
  omega

/-- Memory projection retains actual dispatch positions and converts checked byte
addresses to whole-word indices. It applies only to this strong GPU/global slice. -/
def memoryProjection (event : Mixed.Event) : Option Ptx.Occurrence :=
  event.memory.map fun effect =>
    ⟨some 0, event.pc, ⟨match effect.kind with
      | .load => .load .relaxed | .store => .store .relaxed,
      effect.address.toNat / 4, effect.value⟩⟩

def memoryWitness (s : State) (h : Initial s) (out : Word) : Ptx.Graph (s.memory.length + 4) :=
  Ptx.AffineMemory.witnessAt s.memory (fun i => s.addrs i.val) (s.addrs 3)
    (fun i => h.2 i.castSucc) (h.2 3) out

theorem memoryWitness_valid (s : State) (h : Initial s) (out : Word) :
    (memoryWitness s h out).Valid := Ptx.AffineMemory.witnessAt_valid _ _ _ _ _ _

private theorem input_get (s : State) (h : Initial s) (i : Fin 3) :
    input s i.val = s.memory[(s.addrs i.val).toNat / 4]'(h.2 i.castSucc).2 := by
  have bounded : (s.addrs i.val).toNat / 4 < s.memory.length := (h.2 i.castSucc).2
  simp only [input, List.getElem!_eq_getElem?_getD]
  rw [List.getElem?_eq_getElem bounded]
  rfl

/-- These four graph events are projected from the actual complete instruction
trace; initialization is supplied separately by the caller's initial arena. -/
theorem trace_memory_witness (s : State) (h : Initial s) (mid out : Word) :
    (trace s mid out).filterMap memoryProjection =
      List.ofFn (fun slot : Fin 4 => (memoryWitness s h out).event
        (Ptx.AffineMemory.programIndex s.memory slot)) := by
  have projected : (trace s mid out).filterMap memoryProjection =
      [⟨some 0, 0, ⟨.load .relaxed, (s.addrs 0).toNat / 4, input s 0⟩⟩,
       ⟨some 0, 1, ⟨.load .relaxed, (s.addrs 1).toNat / 4, input s 1⟩⟩,
       ⟨some 0, 2, ⟨.load .relaxed, (s.addrs 2).toNat / 4, input s 2⟩⟩,
       ⟨some 0, 5, ⟨.store .relaxed, (s.addrs 3).toNat / 4, out⟩⟩] := rfl
  rw [projected]
  have h0 : input s 0 = s.memory[(s.addrs 0).toNat / 4]'(h.2 0).2 := input_get s h 0
  have h1 : input s 1 = s.memory[(s.addrs 1).toNat / 4]'(h.2 1).2 := input_get s h 1
  have h2 : input s 2 = s.memory[(s.addrs 2).toNat / 4]'(h.2 2).2 := input_get s h 2
  simp [memoryWitness, Ptx.AffineMemory.witnessAt, Ptx.AffineMemory.witness,
    Ptx.AffineMemory.graph, List.ofFn_succ, Ptx.AffineMemory.programEvent,
    Ptx.AffineMemory.initialReads, Ptx.AffineMemory.wordIndex, h0, h1, h2]

theorem run_memory_witness (s : State) (target : Ptx.Target) (h : Initial s)
    (eligible : Mixed.Eligible target) (run : Mixed.Run target program s final status events) :
    ∃ mid out, Ptx.Binary32.Error.AffineResults (input s 0) (input s 1) (input s 2) mid out ∧
      final.memory[outputIndex s]? = some out ∧ (memoryWitness s h out).Valid ∧
      events.filterMap memoryProjection = List.ofFn (fun slot : Fin 4 =>
        (memoryWitness s h out).event (Ptx.AffineMemory.programIndex s.memory slot)) := by
  obtain ⟨mid, out, allowed, rfl, _, rfl⟩ := (run_iff s target h eligible _ _ _).1 run
  exact ⟨mid, out, allowed, finish_output s mid out h,
    memoryWitness_valid s h out, trace_memory_witness s h mid out⟩

private def eventReads : Mixed.Event → List Scalar.Register
  | .scalar event => event.reads | .binary32 event => event.reads
private def eventWrites : Mixed.Event → List Scalar.Register
  | .scalar event => event.writes | .binary32 event => event.writes

def eventAt (s : State) (mid out : Word) (position : Fin 7) : Mixed.Event :=
  (trace s mid out)[position.val]'(by rw [trace_length]; exact position.isLt)

/-- A direct register dependency is determined by the actual read/write metadata,
without assuming in its definition that the writer occurs earlier. -/
def RegisterDependency (s : State) (mid out : Word) (writer reader : Fin 7) : Prop :=
  ∃ register, register ∈ eventWrites (eventAt s mid out writer) ∧
    register ∈ eventReads (eventAt s mid out reader)

/-- This program's actual register dependencies are forward. This is a property
of the concrete program, not an extra general PTX no-thin-air axiom. -/
theorem register_dependency_forward (s : State) (mid out : Word) (writer reader : Fin 7)
    (dependency : RegisterDependency s mid out writer reader) : writer.val < reader.val := by
  fin_cases writer <;> fin_cases reader <;>
    simp_all [RegisterDependency, eventWrites, eventReads, eventAt, trace, loadEvent,
      Scalar.occurrence, Scalar.Binary32.occurrence, load, multiply, addition, store, exit,
      Scalar.Instr.plain, Guard.reads, Op.reads, Op.writes, Operand32.reads, Operand64.reads]

theorem register_dependency_acyclic (s : State) (mid out : Word) (position : Fin 7) :
    ¬ Ptx.Path (RegisterDependency s mid out) position position := by
  intro path
  exact Nat.lt_irrefl _ (Ptx.Path.rank_increases Fin.val
    (register_dependency_forward s mid out) path)

/-- Actual values originate in initial loads then multiplication then addition;
metadata verifies every direct register dependency is forward in dispatch order.
Memory-source grounding is the separate reviewed witness, not general PTX sufficiency. -/
theorem run_grounded (s : State) (target : Ptx.Target) (h : Initial s)
    (eligible : Mixed.Eligible target) (run : Mixed.Run target program s final status events) :
    ∃ mid out, Ptx.Binary32.Error.AffineResults (input s 0) (input s 1) (input s 2) mid out ∧
      events = trace s mid out ∧
      (∀ writer reader, RegisterDependency s mid out writer reader → writer.val < reader.val) ∧
      (memoryWitness s h out).Valid := by
  obtain ⟨mid, out, allowed, _, _, ht⟩ := (run_iff s target h eligible _ _ _).1 run
  exact ⟨mid, out, allowed, ht, register_dependency_forward s mid out,
    memoryWitness_valid s h out⟩

/-- Nonzero incoming working registers are overwritten before use. -/
def disjointFixture : State :=
  ⟨0, fun i => BitVec.ofNat 32 (17+i), fun i => BitVec.ofNat 64 (4*i),
    fun i => i % 2 == 0, [0x3fc00000, 0x40000000, 0x3e800000, 0xdeadbeef]⟩

/-- Actual seven-dispatch 1.5*2+0.25 execution stores the exact 3.25 encoding. -/
theorem disjoint_example :
    Mixed.Run ⟨94, 70⟩ program disjointFixture
      (finish disjointFixture 0x40400000 0x40500000) .halted
      (trace disjointFixture 0x40400000 0x40500000) ∧
    (finish disjointFixture 0x40400000 0x40500000).memory =
      [0x3fc00000, 0x40000000, 0x3e800000, 0x40500000] := by
  have initial : Initial disjointFixture := by
    constructor
    · rfl
    · intro i; fin_cases i <;> decide
  refine ⟨(run_iff _ _ initial (by constructor <;> decide) _ _ _).2
    ⟨_, _, ⟨?_, ?_⟩, rfl, rfl, rfl⟩, rfl⟩
  · change Ptx.Binary32.Envelope (Ptx.Binary32.reference .mul 0x3fc00000 0x40000000) 0x40400000
    exact Ptx.Binary32.envelope_self _
  · change Ptx.Binary32.Envelope (Ptx.Binary32.reference .add 0x40400000 0x3e800000) 0x40500000
    exact Ptx.Binary32.envelope_self _

def aliasFixture : State :=
  ⟨0, fun _ => 0xdeadbeef, fun _ => 0, fun _ => true, [0x3f800000]⟩

/-- Every pointer aliases one initial 1.0 word: all three loads precede the store,
which writes the exact 2.0 result of 1.0*1.0+1.0. -/
theorem all_alias_example :
    Mixed.Run ⟨94, 70⟩ program aliasFixture
      (finish aliasFixture 0x3f800000 0x40000000) .halted
      (trace aliasFixture 0x3f800000 0x40000000) ∧
    (finish aliasFixture 0x3f800000 0x40000000).memory = [0x40000000] := by
  have initial : Initial aliasFixture := by
    constructor
    · rfl
    · intro i; exact (by decide : ValidAddress [0x3f800000] 0)
  refine ⟨(run_iff _ _ initial (by constructor <;> decide) _ _ _).2
    ⟨_, _, ⟨?_, ?_⟩, rfl, rfl, rfl⟩, rfl⟩
  · change Ptx.Binary32.Envelope (Ptx.Binary32.reference .mul 0x3f800000 0x3f800000) 0x3f800000
    exact Ptx.Binary32.envelope_self _
  · change Ptx.Binary32.Envelope (Ptx.Binary32.reference .add 0x3f800000 0x3f800000) 0x40000000
    exact Ptx.Binary32.envelope_self _

end Ptx.Scalar.Affine

import Ptx.TraceMemory
import Ptx.ComputedPublicationMachine

/-! The ordered global scalar wrapper instantiated through the common projection.
Its singleton catalogue uses the original aligned word address, so existing
publication graphs retain exactly their labels, read sources and coherence. -/
namespace Ptx.Scalar.Ordered

open Ptx.TraceMemory

def access (program : List Instr) (occ : Scalar.Occurrence) : Option (Access 1) :=
  match program[occ.pc]?, occ.memory with
  | some instruction, some effect =>
    if occ.instruction = instruction.erase ∧ occ.executed = true then
      match instruction.op, effect.kind with
      | .load order _ _, .load =>
        some ⟨⟨0, effect.address.toNat / 4⟩, .load order, effect.value⟩
      | .store order _ _, .store =>
        some ⟨⟨0, effect.address.toNat / 4⟩, .store order, effect.value⟩
      | _, _ => none
    else none
  | _, _ => none

/-- Exact equality with the previously checked actual-step labeling function. -/
theorem label_recover (program : List Instr) (thread position : Nat)
    (occ : Scalar.Occurrence) :
    (TraceMemory.label (access program) position occ).map (Projected.occurrence thread) =
      label program thread position occ := by
  cases hf : program[occ.pc]? with
  | none => simp [access, label, TraceMemory.label, hf]
  | some instruction =>
    cases hm : occ.memory with
    | none => simp [access, label, TraceMemory.label, hf, hm]
    | some effect =>
      by_cases h : occ.instruction = instruction.erase ∧ occ.executed = true
      · cases hop : instruction.op <;> cases hk : effect.kind <;>
          simp [access, label, TraceMemory.label, hf, hm, h, hop, hk,
            Projected.occurrence, Access.effect, AccessKind.op, Location.code]
      · simp [access, label, TraceMemory.label, hf, hm, h]

theorem projection_recover (program : List Instr) (thread : Nat) (trace : List Scalar.Occurrence) :
    (project (access program) trace).map (Projected.occurrence thread) =
      (trace.mapIdx (label program thread)).filterMap id := by
  simp only [project, List.map_filterMap, List.mapIdx_eq_zipIdx_map, List.filterMap_map]
  congr 1
  funext p
  exact label_recover program thread p.2 p.1

theorem run_projection (fuel oracle program start thread) :
    (project (access program) (run fuel oracle program start).trace).map
      (Projected.occurrence thread) = events fuel oracle program start thread :=
  projection_recover _ _ _

/-- The common projection inherits actual fetched instruction and effect origin. -/
theorem access_origin (program occ a) (emitted : access program occ = some a) :
    ∃ instruction effect,
      program[occ.pc]? = some instruction ∧ occ.instruction = instruction.erase ∧
      occ.executed = true ∧ occ.memory = some effect ∧
      a.location.word = effect.address.toNat / 4 ∧ a.value = effect.value ∧
      (match instruction.op, effect.kind with
       | .load order _ _, .load => a.kind = .load order
       | .store order _ _, .store => a.kind = .store order
       | _, _ => False) := by
  have recovered := label_recover program 0 0 occ
  simp only [TraceMemory.label, emitted, Option.map_some] at recovered
  obtain ⟨instruction, effect, hf, hi, he, hm, _, _, ha, hv, hk⟩ :=
    label_origin _ _ _ _ _ recovered.symm
  refine ⟨instruction, effect, hf, hi, he, hm, ?_, hv, ?_⟩
  · simpa [Projected.occurrence, Access.effect, Location.code] using ha
  · cases hop : instruction.op <;> cases hek : effect.kind <;> simp [hop, hek] at hk ⊢
    all_goals cases h : a.kind <;> simp_all [Projected.occurrence, Access.effect, AccessKind.op]

/-- A real successful memory instruction cannot be omitted by this adapter. -/
theorem access_complete (program : List Instr) (instruction : Instr)
    (s next : State) (occ : Scalar.Occurrence) (override : Option Word) (effect : MemoryEffect)
    (fetch : program[s.pc]? = some instruction)
    (step : Scalar.eval override instruction.erase s = .next next occ)
    (memory : occ.memory = some effect) : ∃ a, access program occ = some a := by
  obtain ⟨emitted, hm⟩ := label_complete program 0 0 instruction s next occ override effect fetch step memory
  have recovered := label_recover program 0 0 occ
  rw [hm] at recovered
  cases h : access program occ with
  | none => simp [TraceMemory.label, h] at recovered
  | some a => exact ⟨a, rfl⟩

theorem run_access_complete (fuel : Nat) (oracle : Nat → Option Word)
    (program : List Instr) (start : State) (occ : Scalar.Occurrence)
    (member : occ ∈ (run fuel oracle program start).trace)
    (effect : MemoryEffect) (memory : occ.memory = some effect) :
    ∃ a, access program occ = some a := by
  induction fuel generalizing oracle start with
  | zero => simp [run, runWith] at member
  | succ fuel ih =>
    cases hs : stepWith (oracle 0) (erase program) start with
    | next next event =>
      simp only [run, runWith, hs, List.mem_cons] at member
      rcases member with rfl | member
      · cases hf : program[start.pc]? with
        | none => simp [stepWith, erase, List.getElem?_map, hf] at hs
        | some instruction =>
          have he : Scalar.eval (oracle 0) instruction.erase start = .next next occ := by
            simpa [stepWith, erase, List.getElem?_map, hf] using hs
          exact access_complete program instruction start next occ (oracle 0) effect hf he memory
      · exact ih _ _ member
    | halted final event =>
      simp only [run, runWith, hs, List.mem_singleton] at member
      subst occ
      rw [(step_halted hs).2] at memory
      contradiction
    | fault reason => simp [run, runWith, hs] at member
    | unsupported spelling => simp [run, runWith, hs] at member

/-- The projection covers every actual memory effect at its original dynamic index. -/
theorem run_project_complete (fuel oracle program start)
    (position : Nat) (occ : Scalar.Occurrence) (effect : MemoryEffect)
    (atIndex : (run fuel oracle program start).trace[position]? = some occ)
    (memory : occ.memory = some effect) :
    ∃ a, (⟨position, occ, a⟩ : Projected 1 Scalar.Occurrence) ∈
      project (access program) (run fuel oracle program start).trace := by
  obtain ⟨hi, he⟩ := List.getElem?_eq_some_iff.mp atIndex
  have member : occ ∈ (run fuel oracle program start).trace :=
    List.mem_iff_getElem.mpr ⟨position, hi, he⟩
  obtain ⟨a, ha⟩ := run_access_complete fuel oracle program start occ member effect memory
  exact ⟨a, project_complete _ _ atIndex ha⟩

end Ptx.Scalar.Ordered

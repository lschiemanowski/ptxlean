import PtxBinary32.Sequential
import PtxBinary32.Affine
import PtxBinary32.BackwardError

/-! Four manually selected affine kernel launches for a squared-affine backward.
Saved-forward meaning and real-VJP accuracy are separate numerical obligations. -/
namespace Ptx.Scalar.BackwardPipeline
open Ptx.SequentialStorage Ptx.Scalar.Sequential

structure Data where
  x : Word
  w : Word
  saved : Word
  seed : Word
  dx : Word
  dw : Word
  db : Word
  q : Word
  tail : List Word
  deriving DecidableEq, Repr

def Data.words (data : Data) : List Word :=
  [data.x, data.w, data.saved, data.seed, 0x40000000, 0,
    data.dx, data.dw, data.db, data.q] ++ data.tail

def Data.left (data : Data) (stage : Fin 4) : Word :=
  match stage.val with | 0 => 0x40000000 | 1 => data.q | _ => data.db

def Data.right (data : Data) (stage : Fin 4) : Word :=
  match stage.val with | 0 => data.seed | 1 => data.saved | 2 => data.w | _ => data.x

def Data.update (data : Data) (stage : Fin 4) (out : Word) : Data :=
  match stage.val with
  | 0 => {data with q := out}
  | 1 => {data with db := out}
  | 2 => {data with dx := out}
  | _ => {data with dw := out}

def outputData (data : Data) (q db dx dw : Word) : Data :=
  {data with q := q, db := db, dx := dx, dw := dw}

def arguments (allocation : Nat) (stage index : Fin 4) : Argument :=
  ⟨allocation, match stage.val, index.val with
    | 0, 0 => 16 | 0, 1 => 12 | 0, 2 => 20 | 0, _ => 36
    | 1, 0 => 36 | 1, 1 => 8  | 1, 2 => 20 | 1, _ => 32
    | 2, 0 => 32 | 2, 1 => 4  | 2, 2 => 20 | 2, _ => 24
    | _, 0 => 32 | _, 1 => 0  | _, 2 => 20 | _, _ => 28⟩

def stageStart (data : Data) (allocation : Nat) (stage : Fin 4) (registers : Seed) : State :=
  start registers (arguments allocation stage) data.words

def request (target : Target) (thread : ThreadLocation) (allocation : Nat)
    (stage : Fin 4) (registers : Seed) : Request :=
  ⟨target, Affine.program, thread, allocation, 4, arguments allocation stage, registers⟩

def requests (target : Target) (thread : ThreadLocation) (allocation : Nat)
    (registers : Fin 4 → Seed) : List Request :=
  [request target thread allocation 0 (registers 0),
   request target thread allocation 1 (registers 1),
   request target thread allocation 2 (registers 2),
   request target thread allocation 3 (registers 3)]

def Results (x w saved seed pQ q pDb db pDx dx pDw dw : Word) : Prop :=
  Binary32.Error.AffineResults 0x40000000 seed 0 pQ q ∧
  Binary32.Error.AffineResults q saved 0 pDb db ∧
  Binary32.Error.AffineResults db w 0 pDx dx ∧
  Binary32.Error.AffineResults db x 0 pDw dw

variable {data : Data} {allocation : Nat} {stage : Fin 4} {registers : Seed}
  {target : Target} {thread : ThreadLocation} {final : State} {events : List Mixed.Event}
  {before after : Store}

theorem stage_initial : Affine.Initial (stageStart data allocation stage registers) := by
  constructor
  · rfl
  · intro index
    fin_cases stage <;> fin_cases index <;>
      simp [stageStart, start, arguments, Data.words, ValidAddress]

theorem stage_run_iff (eligible : Mixed.Eligible target) :
    Mixed.Run target Affine.program (stageStart data allocation stage registers) final .halted events ↔
      ∃ product out, Binary32.Error.AffineResults (data.left stage) (data.right stage) 0 product out ∧
        final = Affine.finish (stageStart data allocation stage registers) product out ∧
        events = Affine.trace (stageStart data allocation stage registers) product out := by
  have h := Affine.run_iff (stageStart data allocation stage registers) target stage_initial eligible final .halted events
  fin_cases stage <;>
    simpa [Affine.input, stageStart, start, arguments, Data.words, Data.left, Data.right] using h

theorem finish_words (product out : Word) :
    (Affine.finish (stageStart data allocation stage registers) product out).memory =
      (data.update stage out).words := by
  fin_cases stage <;>
    simp [Affine.finish, Affine.afterAdd, Affine.afterMultiply, Affine.afterBias,
      Affine.afterRight, Affine.afterLeft, Affine.outputIndex, stageStart, start,
      arguments, Data.words, Data.update]

/-- Exact state, trace and storage are consequences of each actual stage run. -/
theorem stage_launch_correct
    (present : before.cells allocation = some ⟨thread.device, data.words⟩)
    (eligible : Mixed.Eligible target)
    (launch : SuccessfulLaunch (request target thread allocation stage registers) before after final events) :
    ∃ product out, Binary32.Error.AffineResults (data.left stage) (data.right stage) 0 product out ∧
      after.cells allocation = some ⟨thread.device, (data.update stage out).words⟩ ∧
      final = Affine.finish (stageStart data allocation stage registers) product out ∧
      events = Affine.trace (stageStart data allocation stage registers) product out := by
  obtain ⟨product, out, allowed, state, trace⟩ := (stage_run_iff eligible).mp (launch.run_from present)
  have written := launch.writeback_lookup present
  refine ⟨product, out, allowed, ?_, state, trace⟩
  simpa only [request, state, finish_words] using written

/-- The construction premise is discharged by the public all-bit existence theorem. -/
theorem stage_of_results
    (present : before.cells allocation = some ⟨thread.device, data.words⟩)
    (eligible : Mixed.Eligible target)
    (allowed : Binary32.Error.AffineResults (data.left stage) (data.right stage) 0 product out) :
    ∃ after final events,
      SuccessfulLaunch (request target thread allocation stage registers) before after final events ∧
      after.cells allocation = some ⟨thread.device, (data.update stage out).words⟩ := by
  have run := (stage_run_iff (data := data) (allocation := allocation) (stage := stage)
    (registers := registers) (final := Affine.finish (stageStart data allocation stage registers) product out)
    (events := Affine.trace (stageStart data allocation stage registers) product out) eligible).mpr
      ⟨product, out, allowed, rfl, rfl⟩
  obtain ⟨after, launch⟩ := launch_exists (request := request target thread allocation stage registers)
    present rfl (fun _ => rfl) run
  refine ⟨after, _, _, launch, ?_⟩
  simpa only [request, finish_words] using launch.writeback_lookup present

/-- Traces retain the actual seven fetched instructions and every checked access. -/
theorem stage_trace_safe
    (present : before.cells allocation = some ⟨thread.device, data.words⟩)
    (eligible : Mixed.Eligible target)
    (launch : SuccessfulLaunch (request target thread allocation stage registers) before after final events) :
    events.length = 7 ∧ events.map Mixed.Event.pc = [0,1,2,3,4,5,6] ∧
      events.map Mixed.Event.instruction = Affine.program ∧
      ∀ event ∈ events, ∀ effect, event.memory = some effect →
        (environment before).accessible thread
          (match effect.kind with | .load => .read | .store => .write)
          (address allocation effect.address) 4 := by
  obtain ⟨product, out, _, _, _, trace⟩ := stage_launch_correct present eligible launch
  refine ⟨by rw [trace]; rfl, by rw [trace]; rfl, by rw [trace]; rfl, ?_⟩
  intro event member effect memory
  exact launch.environment_safe member memory

/-- The full four-stage numerical relation is nonempty for arbitrary input bits. -/
theorem results_exists (x w saved seed : Word) :
    ∃ pQ q pDb db pDx dx pDw dw, Results x w saved seed pQ q pDb db pDx dx pDw dw :=
  Binary32.BackwardError.results_exists x w saved seed

variable {seeds : Fin 4 → Seed}

/-- A chain exposes all four real launches and their independent initial registers. -/
theorem four_launches_iff :
    Chain before (requests target thread allocation seeds) after ↔
    ∃ sQ sDb sDx fQ tQ fDb tDb fDx tDx fDw tDw,
      SuccessfulLaunch (request target thread allocation 0 (seeds 0)) before sQ fQ tQ ∧
      SuccessfulLaunch (request target thread allocation 1 (seeds 1)) sQ sDb fDb tDb ∧
      SuccessfulLaunch (request target thread allocation 2 (seeds 2)) sDb sDx fDx tDx ∧
      SuccessfulLaunch (request target thread allocation 3 (seeds 3)) sDx after fDw tDw := by
  simp only [requests, Chain.cons_iff, Chain.nil_iff]
  constructor
  · rintro ⟨sQ, fQ, tQ, hQ, sDb, fDb, tDb, hDb, sDx, fDx, tDx, hDx, last, fDw, tDw, hDw, same⟩
    subst last
    exact ⟨sQ, sDb, sDx, fQ, tQ, fDb, tDb, fDx, tDx, fDw, tDw, hQ, hDb, hDx, hDw⟩
  · rintro ⟨sQ, sDb, sDx, fQ, tQ, fDb, tDb, fDx, tDx, fDw, tDw, hQ, hDb, hDx, hDw⟩
    exact ⟨sQ, fQ, tQ, hQ, sDb, fDb, tDb, hDb, sDx, fDx, tDx, hDx, after, fDw, tDw, hDw, rfl⟩

/-- Every admitted launch supplies its own exact intermediate state and instruction trace. -/
theorem launches_correct
    (present : before.cells allocation = some ⟨thread.device, data.words⟩)
    (eligible : Mixed.Eligible target)
    (hQ : SuccessfulLaunch (request target thread allocation 0 (seeds 0)) before sQ fQ tQ)
    (hDb : SuccessfulLaunch (request target thread allocation 1 (seeds 1)) sQ sDb fDb tDb)
    (hDx : SuccessfulLaunch (request target thread allocation 2 (seeds 2)) sDb sDx fDx tDx)
    (hDw : SuccessfulLaunch (request target thread allocation 3 (seeds 3)) sDx after fDw tDw) :
    ∃ pQ q pDb db pDx dx pDw dw,
      Results data.x data.w data.saved data.seed pQ q pDb db pDx dx pDw dw ∧
      sQ.cells allocation = some ⟨thread.device, (data.update 0 q).words⟩ ∧
      sDb.cells allocation = some ⟨thread.device, ((data.update 0 q).update 1 db).words⟩ ∧
      sDx.cells allocation = some ⟨thread.device, (((data.update 0 q).update 1 db).update 2 dx).words⟩ ∧
      after.cells allocation = some ⟨thread.device, (outputData data q db dx dw).words⟩ ∧
      fQ = Affine.finish (stageStart data allocation 0 (seeds 0)) pQ q ∧
      tQ = Affine.trace (stageStart data allocation 0 (seeds 0)) pQ q ∧
      fDb = Affine.finish (stageStart (data.update 0 q) allocation 1 (seeds 1)) pDb db ∧
      tDb = Affine.trace (stageStart (data.update 0 q) allocation 1 (seeds 1)) pDb db ∧
      fDx = Affine.finish (stageStart ((data.update 0 q).update 1 db) allocation 2 (seeds 2)) pDx dx ∧
      tDx = Affine.trace (stageStart ((data.update 0 q).update 1 db) allocation 2 (seeds 2)) pDx dx ∧
      fDw = Affine.finish (stageStart (((data.update 0 q).update 1 db).update 2 dx) allocation 3 (seeds 3)) pDw dw ∧
      tDw = Affine.trace (stageStart (((data.update 0 q).update 1 db).update 2 dx) allocation 3 (seeds 3)) pDw dw := by
  obtain ⟨pQ, q, rQ, cQ, fQeq, tQeq⟩ := stage_launch_correct present eligible hQ
  obtain ⟨pDb, db, rDb, cDb, fDbeq, tDbeq⟩ := stage_launch_correct cQ eligible hDb
  obtain ⟨pDx, dx, rDx, cDx, fDxeq, tDxeq⟩ := stage_launch_correct cDb eligible hDx
  obtain ⟨pDw, dw, rDw, cDw, fDweq, tDweq⟩ := stage_launch_correct cDx eligible hDw
  exact ⟨pQ, q, pDb, db, pDx, dx, pDw, dw, ⟨rQ, rDb, rDx, rDw⟩,
    cQ, cDb, cDx, cDw, fQeq, tQeq, fDbeq, tDbeq, fDxeq, tDxeq, fDweq, tDweq⟩

/-- Universal correctness starts from execution, without an assumed output relation. -/
theorem pipeline_correct
    (present : before.cells allocation = some ⟨thread.device, data.words⟩)
    (eligible : Mixed.Eligible target)
    (chain : Chain before (requests target thread allocation seeds) after) :
    ∃ pQ q pDb db pDx dx pDw dw,
      Results data.x data.w data.saved data.seed pQ q pDb db pDx dx pDw dw ∧
      after.cells allocation = some ⟨thread.device, (outputData data q db dx dw).words⟩ := by
  obtain ⟨sQ, sDb, sDx, fQ, tQ, fDb, tDb, fDx, tDx, fDw, tDw, hQ, hDb, hDx, hDw⟩ :=
    four_launches_iff.mp chain
  obtain ⟨pQ, q, pDb, db, pDx, dx, pDw, dw, allowed, _, _, _, written, _⟩ :=
    launches_correct present eligible hQ hDb hDx hDw
  exact ⟨pQ, q, pDb, db, pDx, dx, pDw, dw, allowed, written⟩

/-- Any permitted eight rounded results can be realized by actual kernel launches. -/
theorem pipeline_of_results
    (present : before.cells allocation = some ⟨thread.device, data.words⟩)
    (eligible : Mixed.Eligible target)
    (allowed : Results data.x data.w data.saved data.seed pQ q pDb db pDx dx pDw dw) :
    ∃ after, Chain before (requests target thread allocation seeds) after ∧
      after.cells allocation = some ⟨thread.device, (outputData data q db dx dw).words⟩ := by
  obtain ⟨sQ, fQ, tQ, hQ, cQ⟩ := stage_of_results (stage := 0) (registers := seeds 0) present eligible allowed.1
  obtain ⟨sDb, fDb, tDb, hDb, cDb⟩ := stage_of_results (stage := 1) (registers := seeds 1) cQ eligible allowed.2.1
  obtain ⟨sDx, fDx, tDx, hDx, cDx⟩ := stage_of_results (stage := 2) (registers := seeds 2) cDb eligible allowed.2.2.1
  obtain ⟨after, fDw, tDw, hDw, cDw⟩ := stage_of_results (stage := 3) (registers := seeds 3) cDx eligible allowed.2.2.2
  exact ⟨after, .cons hQ (.cons hDb (.cons hDx (.cons hDw .nil))), cDw⟩

/-- Arbitrary initial bit patterns admit completion; no finiteness or accuracy guard is needed. -/
theorem pipeline_exists
    (present : before.cells allocation = some ⟨thread.device, data.words⟩)
    (eligible : Mixed.Eligible target) :
    ∃ after, Chain before (requests target thread allocation seeds) after := by
  obtain ⟨pQ, q, pDb, db, pDx, dx, pDw, dw, allowed⟩ := results_exists data.x data.w data.saved data.seed
  obtain ⟨after, chain, _⟩ := pipeline_of_results (seeds := seeds) present eligible allowed
  exact ⟨after, chain⟩

/-- The four writebacks leave every other allocation unchanged. -/
theorem pipeline_other_allocation
    (chain : Chain before (requests target thread allocation seeds) after)
    (other : Nat) (different : other ≠ allocation) : after.cells other = before.cells other := by
  obtain ⟨sQ, sDb, sDx, fQ, tQ, fDb, tDb, fDx, tDx, fDw, tDw, hQ, hDb, hDx, hDw⟩ :=
    four_launches_iff.mp chain
  exact (hDw.other_cell different).trans ((hDx.other_cell different).trans
    ((hDb.other_cell different).trans (hQ.other_cell different)))

@[simp] theorem words_tail (data : Data) : data.words.drop 10 = data.tail := rfl

/-- Inputs, constants and the arbitrary arena tail are preserved. -/
theorem pipeline_memory_frame
    (present : before.cells allocation = some ⟨thread.device, data.words⟩)
    (eligible : Mixed.Eligible target)
    (chain : Chain before (requests target thread allocation seeds) after) :
    ∃ cell, after.cells allocation = some cell ∧
      cell.words.take 6 = data.words.take 6 ∧ cell.words.drop 10 = data.tail := by
  obtain ⟨pQ, q, pDb, db, pDx, dx, pDw, dw, _, written⟩ := pipeline_correct present eligible chain
  exact ⟨⟨thread.device, (outputData data q db dx dw).words⟩, written, rfl, rfl⟩

/-- Released identities cannot be reused to admit a later backward stage. -/
theorem stage_after_release_rejected
    (released : release before allocation = some freed) (history : History freed last) :
    ¬ SuccessfulLaunch (request target thread allocation stage registers) last after final events :=
  no_launch_after_release released history

end Ptx.Scalar.BackwardPipeline

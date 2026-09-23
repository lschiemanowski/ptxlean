import Ptx.SequentialStorage
import PtxBinary32.Mixed

/-! Synchronous launches contain actual fetched runs; runtime waiting, visibility
and exclusion of interfering accesses remain external correspondence obligations. -/
namespace Ptx.Scalar.Sequential
open Ptx.SequentialStorage

structure Argument where
  allocation : Nat
  offset : Scalar.Address
  deriving DecidableEq, Repr

structure Seed where
  regs : Nat → Word
  addrs : Nat → Scalar.Address
  preds : Nat → Bool

def start (seed : Seed) (args : Fin n → Argument) (memory : List Word) : State where
  pc := 0
  regs := seed.regs
  addrs := fun index => if h : index < n then (args ⟨index, h⟩).offset else seed.addrs index
  preds := seed.preds
  memory := memory

@[simp] theorem start_pc : (start seed args memory).pc = 0 := rfl
@[simp] theorem start_regs : (start seed args memory).regs = seed.regs := rfl
@[simp] theorem start_preds : (start seed args memory).preds = seed.preds := rfl
@[simp] theorem start_memory : (start seed args memory).memory = memory := rfl

@[simp] theorem start_argument (seed : Seed) (args : Fin n → Argument)
    (memory : List Word) (index : Fin n) :
    (start seed args memory).addrs index.val = (args index).offset := by
  simp [start, index.isLt]

theorem start_other (seed : Seed) (args : Fin n → Argument) (memory : List Word)
    (outside : n ≤ index) : (start seed args memory).addrs index = seed.addrs index := by
  simp [start, Nat.not_lt.mpr outside]

structure Request where
  target : Target
  program : List Mixed.Instr
  thread : ThreadLocation
  allocation : Nat
  arity : Nat
  arguments : Fin arity → Argument
  seed : Seed

/-- An actual halted run, with entry identity/device checks and exact writeback. -/
def SuccessfulLaunch (request : Request) (before after : Store)
    (final : State) (trace : List Mixed.Event) : Prop :=
  ∃ cell : Cell, before.cells request.allocation = some cell ∧
    cell.device = request.thread.device ∧
    (∀ index, (request.arguments index).allocation = request.allocation) ∧
    Mixed.Run request.target request.program
      (start request.seed request.arguments cell.words) final .halted trace ∧
    SequentialStorage.writeback before request.allocation final.memory = some after

namespace SuccessfulLaunch
noncomputable def cell (launch : SuccessfulLaunch request before after final trace) : Cell :=
  launch.choose

theorem present (launch : SuccessfulLaunch request before after final trace) :
    before.cells request.allocation = some launch.cell := launch.choose_spec.1

theorem owner (launch : SuccessfulLaunch request before after final trace) :
    launch.cell.device = request.thread.device := launch.choose_spec.2.1

theorem identities (launch : SuccessfulLaunch request before after final trace) :
    ∀ index, (request.arguments index).allocation = request.allocation := launch.choose_spec.2.2.1

theorem run (launch : SuccessfulLaunch request before after final trace) :
    Mixed.Run request.target request.program
      (start request.seed request.arguments launch.cell.words) final .halted trace :=
  launch.choose_spec.2.2.2.1

theorem writeback (launch : SuccessfulLaunch request before after final trace) :
    SequentialStorage.writeback before request.allocation final.memory = some after :=
  launch.choose_spec.2.2.2.2
end SuccessfulLaunch

/-- Existence requires an actual terminating run, not an output postcondition. -/
theorem launch_exists (present : before.cells request.allocation = some cell)
    (owner : cell.device = request.thread.device)
    (identities : ∀ index, (request.arguments index).allocation = request.allocation)
    (run : Mixed.Run request.target request.program
      (start request.seed request.arguments cell.words) final .halted trace) :
    ∃ after, SuccessfulLaunch request before after final trace := by
  obtain ⟨after, written⟩ := writeback_exists present run.memory_length
  exact ⟨after, ⟨cell, present, owner, identities, run, written⟩⟩

namespace SuccessfulLaunch

theorem exact_writeback (launch : SuccessfulLaunch request before after final trace) :
    after.cells request.allocation = some {launch.cell with words := final.memory} ∧
    final.memory.length = launch.cell.words.length ∧ after.nextId = before.nextId := by
  obtain ⟨cell, present, extent, counter, written, _⟩ := writeback_properties launch.writeback
  have same : cell = launch.cell := Option.some.inj (present.symm.trans launch.present)
  subst cell
  exact ⟨written, extent, counter⟩

/-- Convenient version using a caller's known live cell, without choosing anew. -/
theorem run_from (launch : SuccessfulLaunch request before after final trace)
    (known : before.cells request.allocation = some entry) :
    Mixed.Run request.target request.program
      (start request.seed request.arguments entry.words) final .halted trace := by
  have same : entry = launch.cell := Option.some.inj (known.symm.trans launch.present)
  simpa only [same] using launch.run

theorem writeback_lookup (launch : SuccessfulLaunch request before after final trace)
    (known : before.cells request.allocation = some entry) :
    after.cells request.allocation = some {entry with words := final.memory} := by
  have same : entry = launch.cell := Option.some.inj (known.symm.trans launch.present)
  simpa only [same] using launch.exact_writeback.1

theorem environment_unchanged (launch : SuccessfulLaunch request before after final trace) :
    environment after = environment before := writeback_environment launch.writeback

theorem other_cell (launch : SuccessfulLaunch request before after final trace)
    (different : other ≠ request.allocation) : after.cells other = before.cells other := by
  obtain ⟨_, _, _, _, _, untouched⟩ := writeback_properties launch.writeback
  exact untouched other different

theorem environment_safe (launch : SuccessfulLaunch request before after final trace)
    (member : event ∈ trace) (memory : event.memory = some effect) :
    (environment before).accessible request.thread
      (match effect.kind with | .load => .read | .store => .write)
      (address request.allocation effect.address) 4 := by
  apply (access_iff launch.present).mpr
  exact ⟨launch.owner, launch.run.memory_safe member memory⟩

theorem final_environment_safe (launch : SuccessfulLaunch request before after final trace)
    (member : event ∈ trace) (memory : event.memory = some effect) :
    (environment after).accessible request.thread
      (match effect.kind with | .load => .read | .store => .write)
      (address request.allocation effect.address) 4 := by
  apply (access_iff launch.exact_writeback.1).mpr
  refine ⟨launch.owner, ?_⟩
  have valid := launch.run.memory_safe member memory
  simpa only [ValidAddress, start_memory, launch.exact_writeback.2.1] using valid

theorem word_frame (launch : SuccessfulLaunch request before after final trace)
    (untouched : ∀ event ∈ trace, ¬ Mixed.StoresTo event index) :
    final.memory[index]? = launch.cell.words[index]? := launch.run.frame untouched

theorem storage_step (launch : SuccessfulLaunch request before after final trace) :
    SequentialStorage.Step before after := .writeback launch.writeback

end SuccessfulLaunch

theorem no_launch_absent (absent : before.cells request.allocation = none) :
    ¬ SuccessfulLaunch request before after final trace := by
  intro launch
  have present := launch.present
  rw [absent] at present
  contradiction

theorem no_launch_wrong_owner (present : before.cells request.allocation = some cell)
    (wrong : cell.device ≠ request.thread.device) :
    ¬ SuccessfulLaunch request before after final trace := by
  intro launch
  have same : cell = launch.cell := Option.some.inj (present.symm.trans launch.present)
  exact wrong (same ▸ launch.owner)

theorem no_launch_wrong_identity (index : Fin request.arity)
    (wrong : (request.arguments index).allocation ≠ request.allocation) :
    ¬ SuccessfulLaunch request before after final trace := by
  intro launch
  exact wrong (launch.identities index)

theorem no_launch_after_release
    (released : release before request.allocation = some next)
    (history : History next last) :
    ¬ SuccessfulLaunch request last after final trace :=
  no_launch_absent (released_never_live released history)

inductive Chain : Store → List Request → Store → Prop where
  | nil : Chain before [] before
  | cons : SuccessfulLaunch request before middle final trace →
      Chain middle rest after → Chain before (request :: rest) after

namespace Chain

theorem append (left : Chain before first middle) (right : Chain middle second after) :
    Chain before (first ++ second) after := by
  induction left with
  | nil => exact right
  | cons launch _ ih => exact .cons launch (ih right)

theorem cons_iff : Chain before (request :: rest) after ↔
    ∃ middle final trace, SuccessfulLaunch request before middle final trace ∧
      Chain middle rest after := by
  constructor
  · intro chain
    cases chain with
    | cons launch tail => exact ⟨_, _, _, launch, tail⟩
  · rintro ⟨_, _, _, launch, tail⟩
    exact .cons launch tail

theorem nil_iff : Chain before [] after ↔ after = before := by
  constructor
  · intro chain; cases chain; rfl
  · intro same; subst after; exact .nil

theorem two_iff : Chain before [first, second] after ↔
    ∃ middle final₁ trace₁ final₂ trace₂,
      SuccessfulLaunch first before middle final₁ trace₁ ∧
      SuccessfulLaunch second middle after final₂ trace₂ := by
  simp only [cons_iff, nil_iff]
  constructor
  · rintro ⟨middle, final₁, trace₁, firstRun, last, final₂, trace₂, secondRun, same⟩
    subst last
    exact ⟨middle, final₁, trace₁, final₂, trace₂, firstRun, secondRun⟩
  · rintro ⟨middle, final₁, trace₁, final₂, trace₂, firstRun, secondRun⟩
    exact ⟨middle, final₁, trace₁, firstRun, after, final₂, trace₂, secondRun, rfl⟩

theorem storage_history (chain : Chain before requests after) : History before after := by
  induction chain with
  | nil => exact .nil
  | cons launch _ ih => exact .cons launch.storage_step ih

/-- Preservation along existing runs does not construct their existence. -/
theorem invariant (property : Store → Prop)
    (preserved : ∀ request before after final trace,
      property before → SuccessfulLaunch request before after final trace → property after)
    (chain : Chain before requests after) (initial : property before) : property after := by
  induction chain with
  | nil => exact initial
  | cons launch _ ih => exact ih (preserved _ _ _ _ _ initial launch)

theorem old_absent {id : Nat} (chain : Chain before requests after)
    (issued : id < before.nextId) (absent : before.cells id = none) : after.cells id = none :=
  chain.storage_history.old_absent issued absent

end Chain
end Ptx.Scalar.Sequential

import Ptx.ScalarEnvironment

/-! Serialized logical storage lifetimes. Supplied initialized contents, one device
owner per global arena, and never-reused identities; no hardware allocator model. -/
namespace Ptx.SequentialStorage

structure Cell where
  device : Nat
  words : List Word
  deriving DecidableEq, Repr

structure Store where
  nextId : Nat
  cells : Nat → Option Cell
  bounded : ∀ id, nextId ≤ id → cells id = none

variable {id : Nat}

def empty : Store := ⟨0, fun _ => none, fun _ _ => rfl⟩

theorem live_lt (s : Store) (present : s.cells id = some cell) : id < s.nextId := by
  by_cases h : id < s.nextId
  · exact h
  have absent := s.bounded id (by omega)
  rw [present] at absent
  contradiction

private def replace (s : Store) (id : Nat) (value : Option Cell) (old : id < s.nextId) : Store where
  nextId := s.nextId
  cells := fun index => if index = id then value else s.cells index
  bounded := by
    intro index bound
    have other : index ≠ id := by omega
    simp [other, s.bounded index bound]

def reserve (s : Store) (device : Nat) (words : List Word) : Nat × Store :=
  (s.nextId, {
    nextId := s.nextId + 1
    cells := fun id => if id = s.nextId then some ⟨device, words⟩ else s.cells id
    bounded := by
      intro id bound
      have other : id ≠ s.nextId := by omega
      simp [other, s.bounded id (by omega)] })

def release (s : Store) (id : Nat) : Option Store :=
  match present : s.cells id with
  | none => none
  | some _cell => some (replace s id none (live_lt s present))

def writeback (s : Store) (id : Nat) (words : List Word) : Option Store :=
  match present : s.cells id with
  | none => none
  | some cell => if words.length = cell.words.length then
      some (replace s id (some {cell with words := words}) (live_lt s present))
    else none

@[simp] theorem reserve_id (s : Store) (device : Nat) (words : List Word) :
    (reserve s device words).1 = s.nextId := rfl

@[simp] theorem reserve_counter (s : Store) (device : Nat) (words : List Word) :
    (reserve s device words).2.nextId = s.nextId + 1 := rfl

@[simp] theorem reserve_contents (s : Store) (device : Nat) (words : List Word) :
    (reserve s device words).2.cells s.nextId = some ⟨device, words⟩ := by simp [reserve]

theorem reserve_fresh (s : Store) : s.cells s.nextId = none := s.bounded _ (Nat.le_refl _)

theorem reserve_other (s : Store) (device : Nat) (words : List Word) (other : id ≠ s.nextId) :
    (reserve s device words).2.cells id = s.cells id := by simp [reserve, other]

/-- Successful release identifies a live predecessor and removes only that cell. -/
theorem release_iff (s next : Store) (id : Nat) : release s id = some next ↔
    ∃ cell, s.cells id = some cell ∧ next.nextId = s.nextId ∧
      next.cells id = none ∧ ∀ other, other ≠ id → next.cells other = s.cells other := by
  constructor
  · intro released
    unfold release at released
    split at released
    · contradiction
    · rename_i cell present
      cases released
      exact ⟨cell, present, rfl, by simp [replace], fun other h => by simp [replace, h]⟩
  · rintro ⟨cell, present, count, absent, others⟩
    have cellsEq : next.cells = (replace s id none (live_lt s present)).cells := by
      funext index
      by_cases same : index = id
      · subst index; simp [replace, absent]
      · simp [replace, same, others index same]
    have stateEq : next = replace s id none (live_lt s present) := by
      cases next
      cases s
      simp_all [replace]
    subst next
    unfold release
    split <;> simp_all

/-- Successful writeback preserves owner and extent and changes no other cell. -/
theorem writeback_properties (done : writeback s id words = some next) :
    ∃ cell, s.cells id = some cell ∧ words.length = cell.words.length ∧
      next.nextId = s.nextId ∧ next.cells id = some {cell with words := words} ∧
      ∀ other, other ≠ id → next.cells other = s.cells other := by
  unfold writeback at done
  split at done
  · contradiction
  · rename_i cell present
    split at done
    · rename_i extent
      cases done
      exact ⟨cell, present, extent, rfl, by simp [replace], fun other h => by simp [replace, h]⟩
    · contradiction

theorem writeback_exists (present : s.cells id = some cell)
    (extent : words.length = cell.words.length) : ∃ next, writeback s id words = some next := by
  unfold writeback
  split <;> simp_all

@[simp] theorem release_absent (absent : s.cells id = none) : release s id = none := by
  unfold release
  split <;> simp_all

@[simp] theorem writeback_absent (absent : s.cells id = none) : writeback s id words = none := by
  unfold writeback
  split <;> simp_all

inductive Step : Store → Store → Prop where
  | reserve (s : Store) (device : Nat) (words : List Word) : Step s (reserve s device words).2
  | release {id : Nat} (done : release s id = some next) : Step s next
  | writeback {id : Nat} (done : writeback s id words = some next) : Step s next

inductive History : Store → Store → Prop where
  | nil : History s s
  | cons : Step s middle → History middle last → History s last

theorem Step.counter_mono (step : Step s next) : s.nextId ≤ next.nextId := by
  cases step with
  | reserve => simp
  | release done => rw [(release_iff ..).mp done |>.choose_spec.2.1]; exact Nat.le_refl _
  | writeback done => rw [(writeback_properties done).choose_spec.2.2.1]; exact Nat.le_refl _

/-- An absent previously issued identity cannot be revived by any valid action. -/
theorem Step.old_absent (step : Step s next) (issued : id < s.nextId)
    (absent : s.cells id = none) : next.cells id = none := by
  cases step with
  | reserve => rw [reserve_other _ _ _ (by omega)]; exact absent
  | release done =>
    rename_i selected
    obtain ⟨_, _, _, removed, others⟩ := (release_iff ..).mp done
    by_cases same : id = selected
    · simpa only [same] using removed
    · rw [others id same]; exact absent
  | writeback done =>
    rename_i replacement selected
    obtain ⟨_, present, _, _, _, others⟩ := writeback_properties done
    have different : id ≠ selected := by
      intro same
      subst id
      rw [absent] at present
      contradiction
    rw [others id different]
    exact absent

theorem History.old_absent (history : History s last) (issued : id < s.nextId)
    (absent : s.cells id = none) : last.cells id = none := by
  induction history with
  | nil => exact absent
  | cons step _ ih => exact ih (by have := step.counter_mono; omega) (step.old_absent issued absent)

/-- The identity stays invalid through arbitrarily many later reservations,
releases and writes, not merely in the immediately following state. -/
theorem released_never_live (released : release s id = some next) (history : History next last) :
    last.cells id = none := by
  obtain ⟨cell, present, counter, absent, _⟩ := (release_iff ..).mp released
  exact history.old_absent (by rw [counter]; exact live_lt s present) absent

def Cell.allocation (cell : Cell) : Allocation := {
  space := .global, bytes := 4 * cell.words.length, alignment := 4,
  owner := .device cell.device, readable := true, writable := true, initialized := true }

def environment (s : Store) : Environment := ⟨fun id => (s.cells id).map Cell.allocation⟩
def address (id : Nat) (offset : Scalar.Address) : Ptx.Address := Scalar.arenaAddress id offset

@[simp] theorem access_absent (absent : s.cells id = none) :
    (environment s).checkAccess thread kind (address id offset) 4 = .error .unallocated := by
  simp [Environment.checkAccess, environment, address, Scalar.arenaAddress, absent]

/-- Accesses are checked against live initialized contents and the device owner. -/
theorem access_iff (present : s.cells id = some cell) :
    (environment s).accessible thread kind (address id offset) 4 ↔
      cell.device = thread.device ∧ Scalar.ValidAddress cell.words offset := by
  by_cases owner : cell.device = thread.device
  · have checks : (environment s).checkAccess thread kind (address id offset) 4 =
        (Scalar.arenaEnvironment cell.words thread id).checkAccess thread kind
          (Scalar.arenaAddress id offset) 4 := by
      simp [Environment.checkAccess, environment, address, present,
        Scalar.arenaEnvironment, Scalar.arenaAddress, Cell.allocation, owner]
    unfold Environment.accessible
    rw [checks]
    simpa [Environment.accessible, owner] using Scalar.arena_access_iff cell.words thread id offset kind
  · have reverse : thread.device ≠ cell.device := Ne.symm owner
    simp [Environment.accessible, Environment.checkAccess, environment, address,
      Scalar.arenaAddress, Cell.allocation, present, Allocation.ownerAllows, owner, reverse]

/-- Access through a released identity fails even after later storage operations. -/
theorem released_access_fails (released : release s id = some next) (history : History next last) :
    (environment last).checkAccess thread kind (address id offset) 4 = .error .unallocated :=
  access_absent (released_never_live released history)


theorem release_exists (present : s.cells id = some cell) :
    ∃ next, release s id = some next := by
  unfold release
  split <;> simp_all

theorem writeback_wrong_extent (present : s.cells id = some cell)
    (changed : words.length ≠ cell.words.length) : writeback s id words = none := by
  unfold writeback
  split <;> simp_all

theorem History.counter_mono (history : History s last) : s.nextId ≤ last.nextId := by
  induction history with
  | nil => exact Nat.le_refl _
  | cons step _ ih => exact Nat.le_trans step.counter_mono ih

theorem History.append (first : History s middle) (second : History middle last) :
    History s last := by
  induction first with
  | nil => exact second
  | cons step _ ih => exact .cons step (ih second)

/-- Reallocation after any valid intervening history gives a different identity;
the original handle stays absent and the new allocation has the supplied words. -/
theorem released_reallocated (released : release s id = some next)
    (history : History next last) (device : Nat) (words : List Word) :
    (reserve last device words).1 ≠ id ∧
      (reserve last device words).2.cells id = none ∧
      (reserve last device words).2.cells (reserve last device words).1 = some ⟨device, words⟩ := by
  obtain ⟨cell, present, counter, _, _⟩ := (release_iff ..).mp released
  have old : id < last.nextId := by
    have before := live_lt s present
    have later := history.counter_mono
    omega
  refine ⟨by simp only [reserve_id]; omega, ?_, reserve_contents _ _ _⟩
  exact released_never_live released (history.append (.cons (.reserve last device words) .nil))

/-- Completed fixed-extent writeback changes contents, not allocation access metadata. -/
theorem writeback_environment (done : writeback s id words = some next) :
    environment next = environment s := by
  obtain ⟨cell, present, extent, _, written, others⟩ := writeback_properties done
  unfold environment
  congr 1
  funext other
  by_cases same : other = id
  · subst other
    rw [written, present]
    simp [Cell.allocation, extent]
  · rw [others other same]

/-- The old identity 0 does not alias replacement 1, although both use offset zero. -/
theorem reallocation_example :
    ((release (reserve empty 0 [17]).2 0).map fun freed =>
      let replacement := reserve freed 0 [23]
      (replacement.1, replacement.2.cells 0, replacement.2.cells replacement.1)) =
      some (1, none, some (⟨0, [23]⟩ : Cell)) := rfl

/-- A writeback cannot silently resize a live arena. -/
theorem resize_rejected : writeback (reserve empty 0 [17]).2 0 [23, 42] = none := rfl

/-- Device ownership is checked separately from the validity of the byte offset. -/
theorem foreign_device_rejected :
    (environment (reserve empty 0 [17]).2).checkAccess ⟨1, 0, 0, 0, 0⟩ .read
      (address 0 0) 4 = .error .inaccessible := rfl

end Ptx.SequentialStorage

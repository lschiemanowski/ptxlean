import Ptx.SharedReductionControl

/-! Actual emitted-access safety, independent of source/coherence choices. -/
namespace Ptx.Scalar.SharedReduction.Machine.Safety

/-- The persistent arena selected by a space, not the lane's temporary memory view. -/
def arena (s : State n) : Space → List Word
  | .global => s.global
  | .shared => s.shared

theorem scalar_lengths (reads : Option Word) (thread : Fin n) (space : Option Space)
    (i : Instr) (s : State n) :
    (scalarStep reads thread space i s).state.global.length = s.global.length ∧
    (scalarStep reads thread space i s).state.shared.length = s.shared.length := by
  rcases space with _ | (_ | _)
  all_goals
    simp only [scalarStep]
    split
    · rename_i next event evaluated
      have length := Scalar.eval_memory_length evaluated
      constructor <;> first | exact length | rfl
    · simp [setLane]
    · exact ⟨rfl,rfl⟩
    · exact ⟨rfl,rfl⟩

theorem step_lengths (cfg : Config n) (reads : Option Word) (thread : Fin n) (s : State n) :
    (step cfg reads thread s).state.global.length = s.global.length ∧
    (step cfg reads thread s).state.shared.length = s.shared.length := by
  simp only [step]
  split
  · exact ⟨rfl,rfl⟩
  · split
    · exact ⟨rfl,rfl⟩
    · rename_i instruction fetch
      cases instruction with
      | localStep i => exact scalar_lengths reads thread none i s
      | memory space i => exact scalar_lengths reads thread (some space) i s
      | branch guard destination => simp [dispatch,setLane]
      | exit => simp [dispatch,setLane]
      | sync resource => simp only [dispatch]; split <;> exact ⟨rfl,rfl⟩

theorem run_lengths (cfg : Config n) (reads : Nat → Option Word) (schedule : List (Fin n))
    (s : State n) :
    (runWith cfg reads schedule s).state.global.length = s.global.length ∧
    (runWith cfg reads schedule s).state.shared.length = s.shared.length := by
  induction schedule generalizing reads s with
  | nil => exact ⟨rfl,rfl⟩
  | cons thread rest ih =>
    have tail := ih (fun k => reads (k+1)) (step cfg (reads 0) thread s).state
    have head := step_lengths cfg (reads 0) thread s
    exact ⟨tail.1.trans head.1,tail.2.trans head.2⟩

theorem scalar_memory_safe (reads : Option Word) (thread : Fin n) (selected : Option Space)
    (i : Instr) (s : State n) (seen : Fin n) (block : Block) (space : Space)
    (event : Occurrence) (effect : MemoryEffect)
    (member : .scalar seen block (some space) event ∈ (scalarStep reads thread selected i s).events)
    (memory : event.memory = some effect) : Scalar.ValidAddress (arena s space) effect.address := by
  rcases selected with _ | (_ | _)
  all_goals
    simp only [scalarStep] at member
    split at member
    · rename_i next emitted evaluated
      simp only [List.mem_singleton,Event.scalar.injEq] at member
      obtain ⟨rfl,rfl,eq,rfl⟩ := member
      first
      | contradiction
      | (cases eq; exact Scalar.eval_memory_safe evaluated memory)
    · rename_i next emitted evaluated
      simp only [List.mem_singleton,Event.scalar.injEq] at member
      obtain ⟨rfl,rfl,eq,rfl⟩ := member
      have empty := (Scalar.eval_halted evaluated).2
      rw [empty] at memory
      contradiction
    · simp at member
    · simp at member

theorem step_memory_safe (cfg : Config n) (reads : Option Word) (thread : Fin n) (s : State n)
    (seen : Fin n) (block : Block) (space : Space) (event : Occurrence) (effect : MemoryEffect)
    (member : .scalar seen block (some space) event ∈ (step cfg reads thread s).events)
    (memory : event.memory = some effect) : Scalar.ValidAddress (arena s space) effect.address := by
  simp only [step] at member
  split at member
  · simp at member
  · split at member
    · simp at member
    · rename_i instruction fetch
      cases instruction with
      | localStep i => exact scalar_memory_safe reads thread none i s seen block space event effect member memory
      | memory selected i => exact scalar_memory_safe reads thread (some selected) i s seen block space event effect member memory
      | branch guard destination => simp [dispatch] at member
      | exit => simp [dispatch] at member
      | sync resource =>
        simp only [dispatch] at member
        split at member <;> simp only [List.mem_map] at member
        · simp at member
        all_goals obtain ⟨_,_,impossible⟩ := member; contradiction

/-- Arbitrary candidate values/schedules cannot emit an out-of-bounds or
misaligned access, and the bounds refer to the original supplied arena. -/
theorem run_memory_safe (cfg : Config n) (reads : Nat → Option Word) (schedule : List (Fin n))
    (s : State n) (thread : Fin n) (block : Block) (space : Space)
    (event : Occurrence) (effect : MemoryEffect)
    (member : .scalar thread block (some space) event ∈ (runWith cfg reads schedule s).trace)
    (memory : event.memory = some effect) : Scalar.ValidAddress (arena s space) effect.address := by
  induction schedule generalizing reads s with
  | nil => simp [runWith] at member
  | cons selected rest ih =>
    simp only [runWith,List.mem_append] at member
    rcases member with first | later
    · exact step_memory_safe cfg (reads 0) selected s thread block space event effect first memory
    · have safe := ih _ _ later
      have lengths := step_lengths cfg (reads 0) selected s
      cases space <;> simpa [Scalar.ValidAddress,arena,lengths.1,lengths.2] using safe

end Ptx.Scalar.SharedReduction.Machine.Safety

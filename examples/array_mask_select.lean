import Ptx.ArrayMaskSelect

open Ptx Ptx.Scalar Ptx.Scalar.PureKernel
open Ptx.Scalar.ArrayMaskSelect

-- These computations evaluate the list specification; they do not run PTX on a GPU.
#eval (transform 0xff 99 [0x1234, 0x100, 0, 0xffffffff]).map BitVec.toNat
#eval (transform 0xff 99 []).map BitVec.toNat

-- All other initial registers may contain arbitrary data.
example (s : State) :
    ∃ final events, Run ⟨94, 70⟩ (program 0xff 99)
      (initial s [7, 8] [0x1234, 0x100, 0, 0xffffffff] [9]) final .halted events ∧
      final.memory = [7, 8, 52, 99, 99, 255, 9] ∧ events.length = 43 := by
  obtain ⟨final, events, run, memory, length⟩ :=
    execution (target := ⟨94, 70⟩) s [7, 8] [0x1234, 0x100, 0, 0xffffffff] [9] 0xff 99
      (by simp [Eligible]) (by simp [Bounds])
  exact ⟨final, events, run, memory, length⟩

-- Empty arrays exit even at the end of the arena, where a load would be invalid.
example (s : State) :
    ∃ final events, Run ⟨94, 70⟩ (program 0xff 99)
      (initial s [7, 8] [] []) final .halted events ∧
      final.memory = [7, 8] ∧ events.length = 3 := by
  simpa using empty_execution (target := ⟨94, 70⟩) s [7, 8] [] 0xff 99 (by simp [Eligible])

-- One element: an all-zero mask always chooses the fallback.
example (s : State) (x fallback : Word) :
    ∃ final events, Run ⟨94, 70⟩ (program 0 fallback)
      (initial s [] [x] []) final .halted events ∧
      final.memory = [fallback] ∧ events.length = 13 := by
  simpa [transform, MaskSelect.answer] using
    execution s [] [x] [] 0 fallback (by simp [Eligible]) (by simp [Bounds])

-- Bounds are proved from lengths, without allocating these enormous lists.
example (xs : List Word) (length : xs.length = 2^32) : ¬ Bounds [] xs := by
  simp [Bounds, length]
example (front : List Word) (length : front.length = 2^62 - 1) : ¬ Bounds front [1] := by
  simp [Bounds, length]
example (front : List Word) (length : front.length = 2^62 - 2) : Bounds front [1] := by
  simp [Bounds, length]

#check execution
#check correct
#check prefix_termination
#check no_infinite_execution
#check memory_safe
#check other_memory
#print axioms execution
#print axioms no_infinite_execution

import Ptx.MessagePassing
import Ptx.Checker

/-! Complete classifications quantify over arbitrary word values, source maps,
and coherence choices. Finite witnesses establish the converse directions. -/
namespace Ptx.MessagePassing

/-- Existence of a bounded, memory-compatible execution with these final registers. -/
def Possible (order : LoadOrder) (flag payload : Word) : Prop :=
  ∃ source co, (program order).Admitted registers (oracle flag payload) source co ∧
    result order flag payload = (flag, payload)

theorem source_values (order : LoadOrder) (flag payload : Word) (source co)
    (h : (graph order flag payload source co).Sources) :
    (flag = 0 ∨ flag = 1) ∧ (payload = 0 ∨ payload = 7) := by
  have cases (i : Fin 6) : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 := by omega
  constructor
  · have hs := h.compatible c (by trivial)
    change (graph order flag payload source co).write (source c) ∧
      (graph order flag payload source co).sameAddress (source c) c ∧
      ((graph order flag payload source co).event (source c)).effect.value = flag at hs
    rcases cases (source c) with he | he | he | he | he | he
    all_goals rw [he] at hs
    · have bad : (0 : Nat) = 1 := hs.2.1
      omega
    · exact Or.inl hs.2.2.symm
    · have bad : (0 : Nat) = 1 := hs.2.1
      omega
    · exact Or.inr hs.2.2.symm
    · exact False.elim hs.1
    · exact False.elim hs.1
  · have hs := h.compatible d (by trivial)
    change (graph order flag payload source co).write (source d) ∧
      (graph order flag payload source co).sameAddress (source d) d ∧
      ((graph order flag payload source co).event (source d)).effect.value = payload at hs
    rcases cases (source d) with he | he | he | he | he | he
    all_goals rw [he] at hs
    · exact Or.inl hs.2.2.symm
    · have bad : (1 : Nat) = 0 := hs.2.1
      omega
    · exact Or.inr hs.2.2.symm
    · have bad : (1 : Nat) = 0 := hs.2.1
      omega
    · exact False.elim hs.1
    · exact False.elim hs.1

/-- A single family chooses the relevant initial/program write for each read. -/
def outcomeSource (flagNew payloadNew : Bool) (i : Fin 6) : Fin 6 :=
  if i = c then if flagNew then b else iff
  else if i = d then if payloadNew then a else ip
  else ip

def outcomeFlag (new : Bool) : Word := if new then 1 else 0
def outcomePayload (new : Bool) : Word := if new then 7 else 0

def outcomeGraph (order : LoadOrder) (flagNew payloadNew : Bool) : Graph 6 :=
  graph order (outcomeFlag flagNew) (outcomePayload payloadNew)
    (outcomeSource flagNew payloadNew) witnessCo

/-- Explicit kernel-checked candidates for every admitted row, no certificate supplied. -/
theorem zero_flag_check (order : LoadOrder) (payloadNew : Bool) :
    (outcomeGraph order false payloadNew).check = true := by
  cases order <;> cases payloadNew <;> decide

theorem relaxed_check (flagNew payloadNew : Bool) :
    (outcomeGraph .relaxed flagNew payloadNew).check = true := by
  cases flagNew <;> cases payloadNew <;> decide

theorem acquire_success_check : (outcomeGraph .acquire true true).check = true := by decide

theorem acquire_stale_check : (outcomeGraph .acquire true false).check = false := by decide

theorem possible_of_check (order : LoadOrder) (flagNew payloadNew : Bool)
    (checked : (outcomeGraph order flagNew payloadNew).check = true) :
    Possible order (outcomeFlag flagNew) (outcomePayload payloadNew) := by
  refine ⟨outcomeSource flagNew payloadNew, witnessCo, ⟨?_, (Graph.check_iff _).mp checked⟩, rfl⟩
  simp [Program.Bounded, program, producer, consumer, Instr.address]

/-- Exact outcome set for acquire: no values outside the listed rows are possible. -/
theorem acquire_outcomes (flag payload : Word) :
    Possible .acquire flag payload ↔
      (flag = 0 ∧ payload = 0) ∨ (flag = 0 ∧ payload = 7) ∨ (flag = 1 ∧ payload = 7) := by
  constructor
  · rintro ⟨source, co, ⟨_, valid⟩, _⟩
    obtain ⟨hf, hp⟩ := source_values .acquire flag payload source co valid.sources
    rcases hf with hf | hf
    · rcases hp with hp | hp
      · exact Or.inl ⟨hf, hp⟩
      · exact Or.inr (Or.inl ⟨hf, hp⟩)
    · subst flag
      exact Or.inr (Or.inr ⟨rfl, publication payload source co valid⟩)
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact possible_of_check .acquire false false (zero_flag_check .acquire false)
    · exact possible_of_check .acquire false true (zero_flag_check .acquire true)
    · exact possible_of_check .acquire true true acquire_success_check

/-- Exact outcome set for relaxed, preserving the stale-read execution. -/
theorem relaxed_outcomes (flag payload : Word) :
    Possible .relaxed flag payload ↔
      (flag = 0 ∨ flag = 1) ∧ (payload = 0 ∨ payload = 7) := by
  constructor
  · rintro ⟨source, co, ⟨_, valid⟩, _⟩
    exact source_values .relaxed flag payload source co valid.sources
  · rintro ⟨hf | hf, hp | hp⟩ <;> subst flag <;> subst payload
    · exact possible_of_check .relaxed false false (relaxed_check false false)
    · exact possible_of_check .relaxed false true (relaxed_check false true)
    · exact possible_of_check .relaxed true false (relaxed_check true false)
    · exact possible_of_check .relaxed true true (relaxed_check true true)

end Ptx.MessagePassing

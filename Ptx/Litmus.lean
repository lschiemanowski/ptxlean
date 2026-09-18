import Ptx.Checker

/-!
# Small litmus programs for the restricted memory model

These are derived tests under the same word-addressed, GPU/generic, immediate-store
restrictions as message passing. They are not transcriptions of runnable PTX.
The pattern test exercises both two-operation cases in PTX 9.4 §8.8; same-location
ordering uses §8.10.6, and store buffering demonstrates why §8.10.5 is per-location.
-/
namespace Ptx.Litmus

open Graph
set_option synthInstance.maxSize 2048

def zeroRegisters : Nat → Registers := fun _ _ => 0

namespace StoreBuffering

def left : List Instr := [.store .relaxed 0 1, .load .relaxed 1 0]
def right : List Instr := [.store .relaxed 1 1, .load .relaxed 0 0]
def program : Program := ⟨[0, 0], [left, right]⟩
def oracle (x y : Word) (tid _position : Nat) : Word := if tid = 0 then x else y

def graph (x y : Word) (source : Fin 6 → Fin 6) (co : Fin 6 → Fin 6 → Bool) : Graph 6 :=
  program.graph zeroRegisters (oracle x y) source co

def result (x y : Word) : Word × Word :=
  ((execute left (zeroRegisters 0) (oracle x y 0)).1 0,
   (execute right (zeroRegisters 1) (oracle x y 1)).1 0)

theorem result_eq (x y : Word) : result x y = (x, y) := rfl

def source (e : Fin 6) : Fin 6 := if e = 3 then 1 else 0
def co (a b : Fin 6) : Bool := (a == 0 && b == 2) || (a == 1 && b == 4)
def witness : Graph 6 := graph 0 0 source co

theorem witness_valid : witness.Valid := by
  exact (Graph.check_iff _).mp (by decide)

theorem both_zero_exists : ∃ (x y : Word), ∃ source co,
    program.Admitted zeroRegisters (oracle x y) source co ∧ result x y = (0, 0) := by
  refine ⟨0, 0, source, co, ⟨?_, witness_valid⟩, rfl⟩
  simp [Program.Bounded, program, left, right, Instr.address]

theorem memory_safe (x y : Word) (source co) (index : Fin 6) :
    AccessSafe 2 ((graph x y source co).event index).effect := by
  apply Program.graph_access_safe
  simp [program, left, right, Instr.address]

end StoreBuffering

namespace SameLocation

def thread : List Instr := [.store .relaxed 0 1, .load .relaxed 0 0]
def program : Program := ⟨[0], [thread]⟩
def oracle (value : Word) : Nat → Nat → Word := fun _ _ => value

def graph (value : Word) (source : Fin 3 → Fin 3) (co : Fin 3 → Fin 3 → Bool) : Graph 3 :=
  program.graph zeroRegisters (oracle value) source co

def result (value : Word) : Word :=
  (execute thread (zeroRegisters 0) (oracle value 0)).1 0

theorem result_eq (value : Word) : result value = value := rfl

/-- A same-thread preceding write excludes the initial source for the subsequent read. -/
theorem ordered_read (value : Word) (source co) (valid : (graph value source co).Valid) :
    result value = 1 := by
  let g := graph value source co
  have causes : g.cause 1 2 := Or.inl ⟨Path.edge (Or.inl ⟨(by intro h; cases h), rfl, (by change 0 < 1; decide)⟩), rfl⟩
  have notInitial : source 2 ≠ 0 := by
    intro hs
    have hc := valid.co.initFirst 0 1 rfl (by trivial) rfl (by decide)
    exact valid.no_stale 1 2 (by trivial) (by trivial) rfl causes (by change g.coherence (source _) _; rw [hs]; exact hc)
  have h := valid.sources.compatible 2 (by trivial)
  change g.write (source 2) ∧ g.sameAddress (source 2) 2 ∧
    (g.event (source 2)).effect.value = value at h
  have cases : source 2 = 0 ∨ source 2 = 1 ∨ source 2 = 2 := by omega
  rcases cases with hs | hs | hs
  · exact False.elim (notInitial hs)
  · rw [hs] at h
    exact h.2.2.symm
  · rw [hs] at h
    exact False.elim h.1

theorem stale_impossible (source co) : ¬(graph 0 source co).Valid := by
  intro h
  have bad := ordered_read 0 source co h
  contradiction

def source (_e : Fin 3) : Fin 3 := 1
def co (a b : Fin 3) : Bool := a == 0 && b == 1
def witness : Graph 3 := graph 1 source co

theorem witness_valid : witness.Valid := by
  exact (Graph.check_iff _).mp (by decide)

theorem execution_exists : ∃ value source co,
    program.Admitted zeroRegisters (oracle value) source co ∧ result value = 1 := by
  refine ⟨1, source, co, ⟨?_, witness_valid⟩, rfl⟩
  simp [Program.Bounded, program, thread, Instr.address]

theorem memory_safe (value : Word) (source co) (index : Fin 3) :
    AccessSafe 1 ((graph value source co).event index).effect := by
  apply Program.graph_access_safe
  simp [program, thread, Instr.address]

end SameLocation

namespace ReleasePair

def producer : List Instr :=
  [.store .relaxed 0 7, .store .release 1 1, .store .relaxed 1 2]
def consumer : List Instr :=
  [.load .relaxed 1 0, .load .acquire 1 1, .load .relaxed 0 2]
def program : Program := ⟨[0, 0], [producer, consumer]⟩
def oracle (first second payload : Word) (tid position : Nat) : Word :=
  if tid = 1 then if position = 0 then first else if position = 1 then second else payload else 0

/-- Initial payload/flag 0,1; producer 2,3,4; consumer 5,6,7. -/
def graph (first second payload : Word) (source : Fin 8 → Fin 8)
    (co : Fin 8 → Fin 8 → Bool) : Graph 8 :=
  program.graph zeroRegisters (oracle first second payload) source co

def result (first second payload : Word) : Word × Word × Word :=
  let final := (execute consumer (zeroRegisters 1) (oracle first second payload 1)).1
  (final 0, final 1, final 2)

theorem result_eq (first second payload : Word) :
    result first second payload = (first, second, payload) := rfl

/-- Publication is driven by a relaxed load observing a relaxed store after
the release. The proof explicitly derives the nontrivial release pattern. -/
theorem publication (second payload : Word) (source co)
    (valid : (graph 2 second payload source co).Valid) : payload = 7 := by
  let g := graph 2 second payload source co
  have flagSource : source 5 = 4 := by
    have h := valid.sources.compatible 5 (by trivial)
    change g.write (source 5) ∧ g.sameAddress (source 5) 5 ∧
      (g.event (source 5)).effect.value = 2 at h
    have cases : source 5 = 0 ∨ source 5 = 1 ∨ source 5 = 2 ∨ source 5 = 3 ∨
        source 5 = 4 ∨ source 5 = 5 ∨ source 5 = 6 ∨ source 5 = 7 := by omega
    rcases cases with hs | hs | hs | hs | hs | hs | hs | hs
    · rw [hs] at h
      have bad : (0 : Word) = 2 := h.2.2
      contradiction
    · rw [hs] at h
      have bad : (0 : Word) = 2 := h.2.2
      contradiction
    · rw [hs] at h
      have bad : (0 : Nat) = 1 := h.2.1
      omega
    · rw [hs] at h
      have bad : (1 : Word) = 2 := h.2.2
      contradiction
    · exact hs
    · rw [hs] at h
      exact False.elim h.1
    · rw [hs] at h
      exact False.elim h.1
    · rw [hs] at h
      exact False.elim h.1
  have synchronizes : g.sync 3 6 := by
    refine ⟨by change some 0 ≠ some 1; decide, 4, 5, Or.inr ?_, Or.inr ?_, ?_, ?_⟩
    · exact ⟨rfl, by trivial, (by intro h; cases h), ⟨(by intro h; cases h), rfl, (by change 1 < 2; decide)⟩, rfl⟩
    · exact ⟨by trivial, rfl, ⟨(by intro h; cases h), rfl, (by change 0 < 1; decide)⟩, rfl⟩
    · exact ⟨⟨by trivial, flagSource⟩, ⟨(by intro h; cases h), (by intro h; cases h), rfl⟩⟩
    · exact ⟨(by intro h; cases h), (by intro h; cases h), rfl⟩
  have po23 : g.po 2 3 := ⟨(by intro h; cases h), rfl, (by change 0 < 1; decide)⟩
  have po67 : g.po 6 7 := ⟨(by intro h; cases h), rfl, (by change 1 < 2; decide)⟩
  have ordered : g.base 2 7 :=
    .join (.edge (Or.inl po23))
      (.join (.edge (Or.inr synchronizes)) (.edge (Or.inl po67)))
  have causes : g.cause 2 7 := Or.inl ⟨ordered, rfl⟩
  have notInitial : source 7 ≠ 0 := by
    intro hs
    have hc := valid.co.initFirst 0 2 rfl (by trivial) rfl (by decide)
    exact valid.no_stale 2 7 (by trivial) (by trivial) rfl causes (by change g.coherence (source _) _; rw [hs]; exact hc)
  have h := valid.sources.compatible 7 (by trivial)
  change g.write (source 7) ∧ g.sameAddress (source 7) 7 ∧
    (g.event (source 7)).effect.value = payload at h
  have cases : source 7 = 0 ∨ source 7 = 1 ∨ source 7 = 2 ∨ source 7 = 3 ∨
      source 7 = 4 ∨ source 7 = 5 ∨ source 7 = 6 ∨ source 7 = 7 := by omega
  rcases cases with hs | hs | hs | hs | hs | hs | hs | hs
  · exact False.elim (notInitial hs)
  · rw [hs] at h
    have bad : (1 : Nat) = 0 := h.2.1
    omega
  · rw [hs] at h
    exact h.2.2.symm
  · rw [hs] at h
    have bad : (1 : Nat) = 0 := h.2.1
    omega
  · rw [hs] at h
    have bad : (1 : Nat) = 0 := h.2.1
    omega
  · rw [hs] at h
    exact False.elim h.1
  · rw [hs] at h
    exact False.elim h.1
  · rw [hs] at h
    exact False.elim h.1

theorem publication_observed (first second payload : Word) (source co)
    (valid : (graph first second payload source co).Valid)
    (observed : (result first second payload).1 = 2) :
    (result first second payload).2.2 = 7 := by
  change first = 2 at observed
  subst first
  exact publication second payload source co valid

def source (e : Fin 8) : Fin 8 := if e = 5 ∨ e = 6 then 4 else if e = 7 then 2 else 0
def co (a b : Fin 8) : Bool :=
  (a == 0 && b == 2) || (a == 1 && (b == 3 || b == 4)) || (a == 3 && b == 4)
def witness : Graph 8 := graph 2 2 7 source co

theorem witness_valid : witness.Valid := by
  exact (Graph.check_iff _).mp (by decide)

/-- Neither flag load directly observes the release operation in this witness. -/
theorem no_direct_release_observation :
    ¬witness.observation 3 5 ∧ ¬witness.observation 3 6 := by decide

theorem execution_exists : ∃ first second payload source co,
    program.Admitted zeroRegisters (oracle first second payload) source co ∧
    result first second payload = (2, 2, 7) := by
  refine ⟨2, 2, 7, source, co, ⟨?_, witness_valid⟩, rfl⟩
  simp [Program.Bounded, program, producer, consumer, Instr.address]

theorem memory_safe (first second payload : Word) (source co) (index : Fin 8) :
    AccessSafe 2 ((graph first second payload source co).event index).effect := by
  apply Program.graph_access_safe
  simp [program, producer, consumer, Instr.address]

end ReleasePair


namespace AcquirePair

/-- The acquire reads a different thread's relaxed write, not the producer release. -/
def producer : List Instr := [.store .relaxed 0 7, .store .release 1 1]
def consumer : List Instr := [.load .relaxed 1 0, .load .acquire 1 1, .load .relaxed 0 2]
def third : List Instr := [.store .relaxed 1 2]
def program : Program := ⟨[0, 0], [producer, consumer, third]⟩
def oracle (first second payload : Word) (tid position : Nat) : Word :=
  if tid = 1 then if position = 0 then first else if position = 1 then second else payload else 0

/-- Initial payload/flag 0,1; producer 2,3; consumer 4,5,6; third-thread store 7. -/
def graph (first second payload : Word) (source : Fin 8 → Fin 8)
    (co : Fin 8 → Fin 8 → Bool) : Graph 8 :=
  program.graph zeroRegisters (oracle first second payload) source co

def result (first second payload : Word) : Word × Word × Word :=
  let final := (execute consumer (zeroRegisters 1) (oracle first second payload 1)).1
  (final 0, final 1, final 2)

theorem result_eq (first second payload : Word) :
    result first second payload = (first, second, payload) := rfl

/-- Observing the producer release at the earlier relaxed load suffices, even
when the later acquire observes the third thread's independent relaxed store. -/
theorem publication (second payload : Word) (source co)
    (valid : (graph 1 second payload source co).Valid) : payload = 7 := by
  let g := graph 1 second payload source co
  have flagSource : source 4 = 3 := by
    have h := valid.sources.compatible 4 (by trivial)
    change g.write (source 4) ∧ g.sameAddress (source 4) 4 ∧
      (g.event (source 4)).effect.value = 1 at h
    have cases : source 4 = 0 ∨ source 4 = 1 ∨ source 4 = 2 ∨ source 4 = 3 ∨
        source 4 = 4 ∨ source 4 = 5 ∨ source 4 = 6 ∨ source 4 = 7 := by omega
    rcases cases with hs | hs | hs | hs | hs | hs | hs | hs
    · rw [hs] at h
      have bad : (0 : Word) = 1 := h.2.2
      contradiction
    · rw [hs] at h
      have bad : (0 : Word) = 1 := h.2.2
      contradiction
    · rw [hs] at h
      have bad : (0 : Nat) = 1 := h.2.1
      omega
    · exact hs
    · rw [hs] at h
      exact False.elim h.1
    · rw [hs] at h
      exact False.elim h.1
    · rw [hs] at h
      exact False.elim h.1
    · rw [hs] at h
      have bad : (2 : Word) = 1 := h.2.2
      contradiction
  have synchronizes : g.sync 3 5 := by
    refine ⟨by change some 0 ≠ some 1; decide, 3, 4, Or.inl ⟨rfl, rfl⟩, Or.inr ?_, ?_, ?_⟩
    · exact ⟨by trivial, rfl, ⟨(by intro h; cases h), rfl, (by change 0 < 1; decide)⟩, rfl⟩
    · exact ⟨⟨by trivial, flagSource⟩, ⟨(by intro h; cases h), (by intro h; cases h), rfl⟩⟩
    · exact ⟨(by intro h; cases h), (by intro h; cases h), rfl⟩
  have po23 : g.po 2 3 := ⟨(by intro h; cases h), rfl, (by change 0 < 1; decide)⟩
  have po56 : g.po 5 6 := ⟨(by intro h; cases h), rfl, (by change 1 < 2; decide)⟩
  have ordered : g.base 2 6 :=
    .join (.edge (Or.inl po23))
      (.join (.edge (Or.inr synchronizes)) (.edge (Or.inl po56)))
  have causes : g.cause 2 6 := Or.inl ⟨ordered, rfl⟩
  have notInitial : source 6 ≠ 0 := by
    intro hs
    have hc := valid.co.initFirst 0 2 rfl (by trivial) rfl (by decide)
    exact valid.no_stale 2 6 (by trivial) (by trivial) rfl causes
      (by change g.coherence (source 6) 2; rw [hs]; exact hc)
  have h := valid.sources.compatible 6 (by trivial)
  change g.write (source 6) ∧ g.sameAddress (source 6) 6 ∧
    (g.event (source 6)).effect.value = payload at h
  have cases : source 6 = 0 ∨ source 6 = 1 ∨ source 6 = 2 ∨ source 6 = 3 ∨
      source 6 = 4 ∨ source 6 = 5 ∨ source 6 = 6 ∨ source 6 = 7 := by omega
  rcases cases with hs | hs | hs | hs | hs | hs | hs | hs
  · exact False.elim (notInitial hs)
  · rw [hs] at h
    have bad : (1 : Nat) = 0 := h.2.1
    omega
  · rw [hs] at h
    exact h.2.2.symm
  · rw [hs] at h
    have bad : (1 : Nat) = 0 := h.2.1
    omega
  · rw [hs] at h
    exact False.elim h.1
  · rw [hs] at h
    exact False.elim h.1
  · rw [hs] at h
    exact False.elim h.1
  · rw [hs] at h
    have bad : (1 : Nat) = 0 := h.2.1
    omega

theorem publication_observed (first second payload : Word) (source co)
    (valid : (graph first second payload source co).Valid)
    (observed : (result first second payload).1 = 1) :
    (result first second payload).2.2 = 7 := by
  change first = 1 at observed
  subst first
  exact publication second payload source co valid

def source (e : Fin 8) : Fin 8 :=
  if e = 4 then 3 else if e = 5 then 7 else if e = 6 then 2 else 0
def co (a b : Fin 8) : Bool :=
  (a == 0 && b == 2) || (a == 1 && (b == 3 || b == 7)) || (a == 3 && b == 7)
def witness : Graph 8 := graph 1 2 7 source co

theorem witness_valid : witness.Valid := by
  exact (Graph.check_iff _).mp (by decide)

/-- No direct release-to-acquire observation can explain this witness. -/
theorem no_direct_release_observation : ¬witness.observation 3 5 := by decide

theorem execution_exists : ∃ first second payload source co,
    program.Admitted zeroRegisters (oracle first second payload) source co ∧
    result first second payload = (1, 2, 7) := by
  refine ⟨1, 2, 7, source, co, ⟨?_, witness_valid⟩, rfl⟩
  simp [Program.Bounded, program, producer, consumer, third, Instr.address]

theorem memory_safe (first second payload : Word) (source co) (index : Fin 8) :
    AccessSafe 2 ((graph first second payload source co).event index).effect := by
  apply Program.graph_access_safe
  simp [program, producer, consumer, third, Instr.address]

end AcquirePair
/-- Removing the nontrivial release-pattern branch leaves no possible
synchronization pair in the release-pair witness (even without a thread filter). -/
theorem ReleasePair.pair_required : ∀ a b : Fin 8,
    ¬(∃ r, ReleasePair.witness.release a ∧
      ReleasePair.witness.acquirePattern r b ∧
      ReleasePair.witness.observation a r ∧
      ReleasePair.witness.morallyStrong a b) := by decide

/-- Removing the nontrivial acquire-pattern branch likewise eliminates every
possible synchronization pair in the independent acquire-pair witness. -/
theorem AcquirePair.pair_required : ∀ a b : Fin 8,
    ¬(∃ w, AcquirePair.witness.releasePattern a w ∧
      AcquirePair.witness.acquire b ∧
      AcquirePair.witness.observation w b ∧
      AcquirePair.witness.morallyStrong a b) := by decide

theorem ReleasePair.witness_synchronizes : ReleasePair.witness.sync 3 6 := by decide
theorem AcquirePair.witness_synchronizes : AcquirePair.witness.sync 3 5 := by decide

end Ptx.Litmus

import Ptx.Program

/-! Publication, existence, relaxed counterexample, and safety for an actual
straight-line two-thread program. All candidate event labels come from execution. -/
namespace Ptx.MessagePassing

open Graph

set_option synthInstance.maxSize 2048

def producer : List Instr := [.store .relaxed 0 7, .store .release 1 1]
def consumer (order : LoadOrder) : List Instr := [.load order 1 0, .load .relaxed 0 1]
def program (order : LoadOrder) : Program := ⟨[0, 0], [producer, consumer order]⟩
def registers : Nat → Registers := fun _ _ => 0

def oracle (flag payload : Word) (tid position : Nat) : Word :=
  if tid = 1 then if position = 0 then flag else payload else 0

/-- Indices: initial payload, initial flag, payload store, release store,
flag load, payload load. This enumeration is generated, not an input trace. -/
def graph (order : LoadOrder) (flag payload : Word)
    (source : Fin 6 → Fin 6) (co : Fin 6 → Fin 6 → Bool) : Graph 6 :=
  (program order).graph registers (oracle flag payload) source co

abbrev ip : Fin 6 := 0
abbrev iff : Fin 6 := 1
abbrev a : Fin 6 := 2
abbrev b : Fin 6 := 3
abbrev c : Fin 6 := 4
abbrev d : Fin 6 := 5

/-- Explicit trace table, proved by reducing the local execution. -/
theorem events_eq (order : LoadOrder) (flag payload : Word) :
    (program order).events registers (oracle flag payload) =
      [⟨none, 0, ⟨.init, 0, 0⟩⟩, ⟨none, 1, ⟨.init, 1, 0⟩⟩,
       ⟨some 0, 0, ⟨.store .relaxed, 0, 7⟩⟩, ⟨some 0, 1, ⟨.store .release, 1, 1⟩⟩,
       ⟨some 1, 0, ⟨.load order, 1, flag⟩⟩, ⟨some 1, 1, ⟨.load .relaxed, 0, payload⟩⟩] := rfl

/-- Memory safety is a property of every candidate trace, even a rejected one. -/
theorem memory_safe (order : LoadOrder) (flag payload : Word) (source co) (index : Fin 6) :
    AccessSafe 2 ((graph order flag payload source co).event index).effect := by
  apply Program.graph_access_safe
  simp [program, producer, consumer, Instr.address]

/-- The two four-byte objects cannot overlap. -/
theorem objects_disjoint : ¬(InWordFootprint 0 byte ∧ InWordFootprint 1 byte) := by
  intro ⟨h₀,h₁⟩
  exact word_footprints_disjoint (by decide) h₀ h₁

/-- The publication property quantifies over all compatible source and coherence
choices, rather than selecting one witness or assuming the desired payload equality. -/
theorem publication (payload : Word) (source co)
    (valid : (graph .acquire 1 payload source co).Valid) : payload = 7 := by
  let g := graph .acquire 1 payload source co
  have flagSource : source c = b := by
    have h := valid.sources.compatible c (by trivial)
    change g.write (source c) ∧ g.sameAddress (source c) c ∧
      (g.event (source c)).effect.value = 1 at h
    have cases : source c = 0 ∨ source c = 1 ∨ source c = 2 ∨
        source c = 3 ∨ source c = 4 ∨ source c = 5 := by omega
    rcases cases with h' | h' | h' | h' | h' | h'
    · rw [h'] at h
      have bad : (0 : Word) = 1 := h.2.2
      exact False.elim (by contradiction)
    · rw [h'] at h
      have bad : (0 : Word) = 1 := h.2.2
      exact False.elim (by contradiction)
    · rw [h'] at h
      have bad : (0 : Nat) = 1 := h.2.1
      omega
    · exact h'
    · rw [h'] at h
      exact False.elim h.1
    · rw [h'] at h
      exact False.elim h.1
  have synchronizes : g.sync b c := by
    refine ⟨by change some 0 ≠ some 1; decide, b, c, Or.inl ⟨rfl, rfl⟩, Or.inl ⟨rfl, rfl⟩, ?_, ?_⟩
    · exact ⟨⟨by trivial, flagSource⟩, by exact ⟨(by intro h; cases h), (by intro h; cases h), rfl⟩⟩
    · exact ⟨(by intro h; cases h), (by intro h; cases h), rfl⟩
  have ordered : g.base a d :=
    .join (.edge (Or.inl (by exact ⟨(by intro h; cases h), rfl, Nat.zero_lt_one⟩)))
      (.join (.edge (Or.inr synchronizes)) (.edge (Or.inl (by exact ⟨(by intro h; cases h), rfl, Nat.zero_lt_one⟩))))
  have causes : g.cause a d := Or.inl ⟨ordered, rfl⟩
  have notInitial : source d ≠ ip := by
    intro hs
    have hc := valid.co.initFirst ip a rfl (by trivial) rfl (by decide)
    exact valid.no_stale a d (by trivial) (by trivial) rfl causes (by change g.coherence (source d) a; rw [hs]; exact hc)
  have h := valid.sources.compatible d (by trivial)
  change g.write (source d) ∧ g.sameAddress (source d) d ∧
    (g.event (source d)).effect.value = payload at h
  have cases : source d = 0 ∨ source d = 1 ∨ source d = 2 ∨
      source d = 3 ∨ source d = 4 ∨ source d = 5 := by omega
  rcases cases with h' | h' | h' | h' | h' | h'
  · exact False.elim (notInitial h')
  · rw [h'] at h
    have bad : (1 : Nat) = 0 := h.2.1
    omega
  · rw [h'] at h
    exact h.2.2.symm
  · rw [h'] at h
    have bad : (1 : Nat) = 0 := h.2.1
    omega
  · rw [h'] at h
    exact False.elim h.1
  · rw [h'] at h
    exact False.elim h.1

/-- Only nontrivial coherence edges are initialization before its program store. -/
def witnessCo (x y : Fin 6) : Bool := (x == ip && y == a) || (x == iff && y == b)
def successSource (x : Fin 6) : Fin 6 := if x = c then b else if x = d then a else ip
def staleSource (x : Fin 6) : Fin 6 := if x = c then b else ip

def success : Graph 6 := graph .acquire 1 7 successSource witnessCo
def stale : Graph 6 := graph .relaxed 1 0 staleSource witnessCo

def successUpper (x y : Fin 6) : Prop := 2 ≤ x.val ∧ x.val < y.val
def staleUpper (x y : Fin 6) : Prop := (x = a ∧ y = b) ∨ (x = c ∧ y = d)
def staleRank (x : Fin 6) : Nat := if x = a ∨ x = c then 2 else if x = b ∨ x = d then 1 else 0

/-- Unfold the finite relations; the kernel checks the resulting decision proof. This never uses native evaluation. -/
local macro "finite_check" : tactic => `(tactic|
  (simp only [Graph.baseEdge, Graph.sync, Graph.releasePattern, Graph.acquirePattern,
    Graph.observation, Graph.rf, Graph.morallyStrong, Graph.initial, Graph.release,
    Graph.acquire, Graph.po, Graph.sameAddress,
    Graph.coherence, Graph.upperCause, Graph.locationEdge, Graph.communication,
    successUpper, staleUpper] <;> decide))

/-- Kernel-reduced finite obligations certify the successful witness. -/
theorem success_valid : success.Valid := by
  apply valid_of_certificate (upper := successUpper) (rank := Fin.val)
  exact {
    sources := ⟨by finite_check⟩
    co := ⟨by finite_check, by finite_check, by finite_check, by finite_check, by finite_check⟩
    edge_included := by finite_check
    upper_trans := by finite_check
    upper_irrefl := by finite_check
    coherence_cause := by finite_check
    no_future := by finite_check
    no_stale := by finite_check
    location_rank := by finite_check
  }

/-- The same program with a relaxed flag load admits flag=1, payload=0. -/
theorem stale_valid : stale.Valid := by
  apply valid_of_certificate (upper := staleUpper) (rank := staleRank)
  exact {
    sources := ⟨by finite_check⟩
    co := ⟨by finite_check, by finite_check, by finite_check, by finite_check, by finite_check⟩
    edge_included := by finite_check
    upper_trans := by finite_check
    upper_irrefl := by finite_check
    coherence_cause := by finite_check
    no_future := by finite_check
    no_stale := by finite_check
    location_rank := by finite_check
  }

/-- Observable values are the actual final consumer registers. -/
def result (order : LoadOrder) (flag payload : Word) : Word × Word :=
  let final := (execute (consumer order) (registers 1) (oracle flag payload 1)).1
  (final 0, final 1)

theorem result_eq (order : LoadOrder) (flag payload : Word) :
    result order flag payload = (flag, payload) := rfl

theorem publication_observed (flag payload : Word) (source co)
    (valid : (graph .acquire flag payload source co).Valid)
    (observed : (result .acquire flag payload).1 = 1) :
    (result .acquire flag payload).2 = 7 := by
  change flag = 1 at observed
  subst flag
  exact publication payload source co valid

/-- Two completed local runs, coupled to the same oracle used by graph labels. -/
theorem local_completion (order : LoadOrder) (flag payload : Word) :
    Runs producer (registers 0) (oracle flag payload 0)
      (execute producer (registers 0) (oracle flag payload 0)).1
      (execute producer (registers 0) (oracle flag payload 0)).2 ∧
    Runs (consumer order) (registers 1) (oracle flag payload 1)
      (execute (consumer order) (registers 1) (oracle flag payload 1)).1
      (execute (consumer order) (registers 1) (oracle flag payload 1)).2 :=
  ⟨execute_runs _ _ _, execute_runs _ _ _⟩

/-- Existence includes the actual completed program and final register result. -/
theorem successful_execution_exists : ∃ (flag payload : Word), ∃ source co,
    (program .acquire).Admitted registers (oracle flag payload) source co ∧
    result .acquire flag payload = (1, 7) := by
  refine ⟨1, 7, successSource, witnessCo, ⟨?_, success_valid⟩, rfl⟩
  simp [Program.Bounded, program, producer, consumer, Instr.address]

theorem relaxed_counterexample_exists : ∃ (flag payload : Word), ∃ source co,
    (program .relaxed).Admitted registers (oracle flag payload) source co ∧
    result .relaxed flag payload = (1, 0) := by
  refine ⟨1, 0, staleSource, witnessCo, ⟨?_, stale_valid⟩, rfl⟩
  simp [Program.Bounded, program, producer, consumer, Instr.address]

/-- Qualifier strengthening rejects this concrete bad result for every choice. -/
theorem acquire_stale_impossible (source co) :
    ¬(graph .acquire 1 0 source co).Valid := by
  intro valid
  have bad := publication 0 source co valid
  contradiction

end Ptx.MessagePassing

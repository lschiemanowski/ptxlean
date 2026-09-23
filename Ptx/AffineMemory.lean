import Ptx.ScalarMemoryWitness

/-! Abstract three-load/one-store memory graphs with unrestricted full-word aliases.
No arithmetic or actual mixed-trace correspondence is assumed or claimed here. -/
namespace Ptx.AffineMemory


variable {memory : List Word}

abbrev Index (memory : List Word) := Fin (memory.length + 4)

def initIndex (memory : List Word) (address : Fin memory.length) : Index memory :=
  ⟨address.val, by omega⟩

def programIndex (memory : List Word) (slot : Fin 4) : Index memory :=
  ⟨memory.length + slot.val, by have := slot.isLt; omega⟩

theorem index_cases (i : Index memory) :
    (∃ a, i = initIndex memory a) ∨ i = programIndex memory 0 ∨
    i = programIndex memory 1 ∨ i = programIndex memory 2 ∨ i = programIndex memory 3 := by
  by_cases h : i.val < memory.length
  · exact Or.inl ⟨⟨i.val, h⟩, rfl⟩
  · have hi := i.isLt
    simp only [programIndex, Fin.ext_iff]
    omega

def programEvent (inputs : Fin 3 → Fin memory.length) (output : Fin memory.length)
    (reads : Fin 3 → Word) (stored : Word) : Nat → Occurrence
  | 0 => ⟨some 0, 0, ⟨.load .relaxed, (inputs 0).val, reads 0⟩⟩
  | 1 => ⟨some 0, 1, ⟨.load .relaxed, (inputs 1).val, reads 1⟩⟩
  | 2 => ⟨some 0, 2, ⟨.load .relaxed, (inputs 2).val, reads 2⟩⟩
  | _ => ⟨some 0, 5, ⟨.store .relaxed, output.val, stored⟩⟩

def event (memory : List Word) (inputs : Fin 3 → Fin memory.length)
    (output : Fin memory.length) (reads : Fin 3 → Word) (stored : Word)
    (i : Index memory) : Occurrence :=
  if h : i.val < memory.length then
    ⟨none, i.val, ⟨.init, i.val, memory[i.val]⟩⟩
  else programEvent inputs output reads stored (i.val - memory.length)

@[simp] theorem event_init (a : Fin memory.length) :
    event memory inputs output reads stored (initIndex memory a) =
      ⟨none, a.val, ⟨.init, a.val, memory[a.val]⟩⟩ := by
  simp [event, initIndex, a.isLt]

@[simp] theorem event_program (slot : Fin 4) :
    event memory inputs output reads stored (programIndex memory slot) =
      programEvent inputs output reads stored slot.val := by
  simp [event, programIndex, Nat.not_lt.mpr (Nat.le_add_right _ _)]

def graph (memory : List Word) (inputs : Fin 3 → Fin memory.length)
    (output : Fin memory.length) (reads : Fin 3 → Word) (stored : Word)
    (source : Index memory → Index memory) (co : Index memory → Index memory → Bool) :
    Graph (memory.length + 4) := ⟨event memory inputs output reads stored, source, co⟩

def initialReads (memory : List Word) (inputs : Fin 3 → Fin memory.length) : Fin 3 → Word :=
  fun slot => memory[(inputs slot).val]

def witnessSource (memory : List Word) (inputs : Fin 3 → Fin memory.length)
    (output : Fin memory.length) (i : Index memory) : Index memory :=
  if i = programIndex memory 0 then initIndex memory (inputs 0)
  else if i = programIndex memory 1 then initIndex memory (inputs 1)
  else if i = programIndex memory 2 then initIndex memory (inputs 2)
  else initIndex memory output

def witnessCo (memory : List Word) (output : Fin memory.length)
    (a b : Index memory) : Bool :=
  decide (a = initIndex memory output ∧ b = programIndex memory 3)

def witness (memory : List Word) (inputs : Fin 3 → Fin memory.length)
    (output : Fin memory.length) (stored : Word) : Graph (memory.length + 4) :=
  graph memory inputs output (initialReads memory inputs) stored
    (witnessSource memory inputs output) (witnessCo memory output)

def upper (a b : Index memory) : Prop := memory.length ≤ a.val ∧ a.val < b.val

@[simp] theorem init_program_ne (a : Fin memory.length) (slot : Fin 4) :
    initIndex memory a ≠ programIndex memory slot := by
  intro h
  have he := congrArg Fin.val h
  have := a.isLt
  simp only [initIndex, programIndex] at he
  omega

@[simp] theorem program_init_ne (a : Fin memory.length) (slot : Fin 4) :
    programIndex memory slot ≠ initIndex memory a := Ne.symm (init_program_ne a slot)

@[simp] theorem initIndex_inj (a b : Fin memory.length) :
    initIndex memory a = initIndex memory b ↔ a = b := by
  simp [initIndex, Fin.ext_iff]

@[simp] theorem programIndex_inj (a b : Fin 4) :
    programIndex memory a = programIndex memory b ↔ a = b := by
  simp [programIndex, Fin.ext_iff]

local macro "cases_event" i:ident : tactic =>
  `(tactic| (rcases index_cases $i with ⟨initialAddress, equality⟩ | equality | equality | equality | equality) <;> subst $i)

@[simp] theorem witness_no_observation (a b : Index memory) :
    ¬(witness memory inputs output stored).observation a b := by
  cases_event b <;>
    simp [Graph.observation, Graph.rf, Graph.read, Graph.morallyStrong, Graph.initial,
      witness, graph, programEvent, witnessSource, eq_comm]
  all_goals intro equality; subst a; simp

local macro "reduce_graph" : tactic => `(tactic|
  (try simp only [Graph.upperCause, witness_no_observation, false_and, exists_const, or_false]
   simp [Graph.baseEdge, Graph.sync, Graph.releasePattern, Graph.acquirePattern,
    Graph.observation, Graph.rf, Graph.morallyStrong, Graph.initial, Graph.release,
    Graph.acquire, Graph.po, Graph.sameAddress, Graph.read, Graph.write,
    Graph.coherence, Graph.upperCause, Graph.locationEdge, Graph.communication,
    witness, graph, event_init, event_program, programEvent, initialReads,
    witnessSource, witnessCo, upper]
   all_goals try simp_all [Fin.ext_iff, initIndex, programIndex]
   all_goals omega))

/-- Every alias pattern admits an initialization-sourced memory graph. -/
theorem witness_valid (memory : List Word) (inputs : Fin 3 → Fin memory.length)
    (output : Fin memory.length) (stored : Word) : (witness memory inputs output stored).Valid := by
  apply Graph.valid_of_certificate (upper := upper) (rank := Fin.val)
  refine {
    sources := ⟨?_⟩
    co := ⟨?_, ?_, ?_, ?_, ?_⟩
    edge_included := ?_
    upper_trans := ?_
    upper_irrefl := ?_
    coherence_cause := ?_
    no_future := ?_
    no_stale := ?_
    location_rank := ?_ }
  · intro r; cases_event r <;> reduce_graph
  · intro a b; cases_event a <;> cases_event b <;> reduce_graph
  · intro a; cases_event a <;> reduce_graph
  · intro a b c; cases_event a <;> cases_event b <;> cases_event c <;> reduce_graph
  · intro a b; cases_event a <;> cases_event b <;> reduce_graph
  · intro a b; cases_event a <;> cases_event b <;> reduce_graph
  · intro a b; cases_event a <;> cases_event b <;> reduce_graph
  · intro a b c; unfold upper; omega
  · intro a; unfold upper; omega
  · intro a b; cases_event a <;> cases_event b <;> reduce_graph
  · intro a b; cases_event a <;> cases_event b <;> reduce_graph
  · intro a b hw hr _ hc
    have hu : upper a b := by
      exact (by simpa only [Graph.upperCause, witness_no_observation, false_and,
        exists_const, or_false] using hc : upper a b ∧ _).1
    cases_event a <;> cases_event b <;>
      simp [Graph.write, Graph.read, witness, graph, programEvent] at hw hr
    all_goals simp only [upper, initIndex, programIndex] at hu
    all_goals omega
  · intro a b; cases_event a <;> cases_event b <;> reduce_graph


@[simp] theorem event_read (slot : Fin 3) :
    event memory inputs output reads stored (programIndex memory slot.castSucc) =
      ⟨some 0, slot.val, ⟨.load .relaxed, (inputs slot).val, reads slot⟩⟩ := by
  have h : slot = 0 ∨ slot = 1 ∨ slot = 2 := by
    have := slot.isLt
    simp only [Fin.ext_iff]
    omega
  rcases h with rfl | rfl | rfl <;> simp [programEvent]

/-- A read before the sole store cannot choose it, even at the same address. -/
theorem source_initial_of_before_store
    (valid : (graph memory inputs output reads stored source co).Valid)
    (r : Index memory)
    (isRead : (graph memory inputs output reads stored source co).read r)
    (before : (graph memory inputs output reads stored source co).po r (programIndex memory 3)) :
    ∃ a, source r = initIndex memory a := by
  have compatible := valid.sources.compatible r isRead
  rcases index_cases (source r) with hi | h | h | h | h
  · exact hi
  · simpa [Graph.write, graph, h, programEvent] using compatible.1
  · simpa [Graph.write, graph, h, programEvent] using compatible.1
  · simpa [Graph.write, graph, h, programEvent] using compatible.1
  · have same : (graph memory inputs output reads stored source co).sameAddress r
        (programIndex memory 3) := by
      have hs := compatible.2.1
      change (event memory inputs output reads stored (source r)).effect.address = _ at hs
      rw [h] at hs
      exact hs.symm
    have forbidden := valid.no_future r (programIndex memory 3) isRead
      (by simp [Graph.write, graph, programEvent]) same
      (Or.inl ⟨Path.edge (Or.inl before), same⟩)
    exact False.elim (forbidden h)

/-- Full graph validity forces the initial values; source identity is derived. -/
theorem valid_reads_initial
    (valid : (graph memory inputs output reads stored source co).Valid) :
    reads = initialReads memory inputs := by
  funext slot
  let r := programIndex memory slot.castSucc
  have isRead : (graph memory inputs output reads stored source co).read r := by
    simp only [Graph.read, graph, r, event_read]
  have before : (graph memory inputs output reads stored source co).po r
      (programIndex memory 3) := by
    simp only [Graph.po, graph, r, event_read]
    simp [programEvent]
    omega
  obtain ⟨a, sourceEq⟩ := source_initial_of_before_store valid r isRead before
  have compatible := valid.sources.compatible r isRead
  change Graph.write _ _ ∧
    (event memory inputs output reads stored (source r)).effect.address =
      (event memory inputs output reads stored r).effect.address ∧
    (event memory inputs output reads stored (source r)).effect.value =
      (event memory inputs output reads stored r).effect.value at compatible
  rw [sourceEq] at compatible
  simp only [r, event_init, event_read] at compatible
  have addressEq : a = inputs slot := Fin.ext compatible.2.1
  simpa [initialReads, addressEq] using compatible.2.2.symm

/-- The constructed read sources and program order are grounded in earlier indices. -/
theorem witness_grounding_rank (a b : Index memory) :
    (witness memory inputs output stored).po a b ∨
      (witness memory inputs output stored).rf a b → a.val < b.val := by
  cases_event a <;> cases_event b <;> reduce_graph

theorem witness_grounding_acyclic (a : Index memory) :
    ¬Path (fun a b => (witness memory inputs output stored).po a b ∨
      (witness memory inputs output stored).rf a b) a a := by
  intro path
  exact Nat.lt_irrefl _ (Path.rank_increases Fin.val witness_grounding_rank path)

/-- Resolve a checked byte offset to its unique whole-word location. -/
def wordIndex (address : Scalar.Address) (valid : Scalar.ValidAddress memory address) :
    Fin memory.length := ⟨address.toNat / 4, valid.2⟩

theorem wordIndex_bytes (address : Scalar.Address) (valid : Scalar.ValidAddress memory address) :
    4 * (wordIndex address valid).val = address.toNat := by
  have division := Nat.mod_add_div address.toNat 4
  simpa [wordIndex, valid.1] using division

def witnessAt (memory : List Word) (inputs : Fin 3 → Scalar.Address)
    (output : Scalar.Address) (validInputs : ∀ i, Scalar.ValidAddress memory (inputs i))
    (validOutput : Scalar.ValidAddress memory output) (stored : Word) :
    Graph (memory.length + 4) :=
  witness memory (fun i => wordIndex (inputs i) (validInputs i))
    (wordIndex output validOutput) stored

theorem witnessAt_valid (memory : List Word) (inputs : Fin 3 → Scalar.Address)
    (output : Scalar.Address) (validInputs : ∀ i, Scalar.ValidAddress memory (inputs i))
    (validOutput : Scalar.ValidAddress memory output) (stored : Word) :
    (witnessAt memory inputs output validInputs validOutput stored).Valid :=
  witness_valid _ _ _ _

/-- All four arguments alias while the final store changes the memory word. -/
theorem all_alias_example :
    (witness [0x3f800000] (fun _ => ⟨0, by decide⟩) ⟨0, by decide⟩ 0x40000000).Valid ∧
    initialReads [0x3f800000] (fun _ => ⟨0, by decide⟩) = (fun _ => 0x3f800000) := by
  exact ⟨witness_valid _ _ _ _, rfl⟩

end Ptx.AffineMemory

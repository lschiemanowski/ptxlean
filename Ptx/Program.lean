import Ptx.Memory

/-!
# Programs supply graph labels

Every graph event is materialized from an arena initialization or a completed
local instruction trace. Candidate sources and coherence are supplied separately;
they cannot introduce instructions, writes, or values into the event collection.
-/

namespace Ptx

structure Program where
  initial : List Word
  threads : List (List Instr)
  deriving DecidableEq, Repr

def threadEvents (tid : Nat) (program : List Instr) (registers : Registers)
    (oracle : Nat → Word) : List Occurrence :=
  (execute program registers oracle).2.mapIdx fun position effect =>
    ⟨some tid, position, effect⟩

def Program.events (p : Program) (registers : Nat → Registers)
    (oracle : Nat → Nat → Word) : List Occurrence :=
  p.initial.mapIdx (fun address value => ⟨none, address, ⟨.init, address, value⟩⟩) ++
    (p.threads.mapIdx fun tid program => threadEvents tid program (registers tid) (oracle tid)).flatten

def Program.graph (p : Program) (registers : Nat → Registers) (oracle : Nat → Nat → Word)
    (source : Fin (p.events registers oracle).length → Fin (p.events registers oracle).length)
    (co : Fin (p.events registers oracle).length → Fin (p.events registers oracle).length → Bool) :
    Graph (p.events registers oracle).length :=
  ⟨fun index => (p.events registers oracle).get index, source, co⟩

/-- All typed accesses are inside the initialized word arena. -/
def Program.Bounded (p : Program) : Prop :=
  ∀ program ∈ p.threads, ∀ instruction ∈ program,
    instruction.address < p.initial.length

/-- Admission combines arena bounds with the derived graph's memory constraints.
Local traces are already materialized by `events`; graph validity alone does not
assert bounds or operational progress of a hardware scheduler. -/
def Program.Admitted (p : Program) (registers : Nat → Registers) (oracle : Nat → Nat → Word)
    (source : Fin (p.events registers oracle).length → Fin (p.events registers oracle).length)
    (co : Fin (p.events registers oracle).length → Fin (p.events registers oracle).length → Bool) :
    Prop :=
  p.Bounded ∧ (p.graph registers oracle source co).Valid

/-- Each actual program thread has the completed local run used to form its events.
This holds for any candidate oracle; global compatibility is checked separately. -/
theorem Program.all_threads_run (p : Program) (registers : Nat → Registers)
    (oracle : Nat → Nat → Word) :
    ∀ (tid : Nat) (ht : tid < p.threads.length),
      Runs p.threads[tid] (registers tid) (oracle tid)
        (execute p.threads[tid] (registers tid) (oracle tid)).1
        (execute p.threads[tid] (registers tid) (oracle tid)).2 := by
  intro tid ht
  exact execute_runs _ _ _

theorem threadEvents_eq (tid : Nat) (program : List Instr) (registers : Registers)
    (oracle : Nat → Word) :
    threadEvents tid program registers oracle =
      program.mapIdx (fun position instruction =>
        ⟨some tid, position, instruction.effect (oracle position)⟩) := by
  simp [threadEvents, execute_effects, Function.comp_def]

theorem threadEvents_origin (h : occurrence ∈ threadEvents tid program registers oracle) :
    ∃ (position : Nat) (hp : position < program.length),
      occurrence = ⟨some tid, position, program[position].effect (oracle position)⟩ := by
  rw [threadEvents_eq] at h
  obtain ⟨position, hp, he⟩ := List.mem_mapIdx.mp h
  exact ⟨position, hp, he.symm⟩

/-- Exhaustive provenance, retaining exact thread and instruction positions. -/
def Program.Origin (p : Program) (oracle : Nat → Nat → Word) (occurrence : Occurrence) : Prop :=
  (∃ (address : Nat) (ha : address < p.initial.length),
    occurrence = ⟨none, address, ⟨.init, address, p.initial[address]⟩⟩) ∨
  (∃ (tid : Nat) (ht : tid < p.threads.length)
      (position : Nat) (hp : position < p.threads[tid].length),
    occurrence = ⟨some tid, position, p.threads[tid][position].effect (oracle tid position)⟩)

variable {p : Program}

theorem Program.events_origin (h : occurrence ∈ p.events registers oracle) :
    p.Origin oracle occurrence := by
  rcases List.mem_append.mp h with hi | ht
  · obtain ⟨address, ha, he⟩ := List.mem_mapIdx.mp hi
    exact Or.inl ⟨address, ha, he.symm⟩
  · obtain ⟨trace, htrace, ho⟩ := List.mem_flatten.mp ht
    obtain ⟨tid, htid, he⟩ := List.mem_mapIdx.mp htrace
    rw [← he] at ho
    obtain ⟨position, hp, hpEq⟩ := threadEvents_origin ho
    exact Or.inr ⟨tid, htid, position, hp, hpEq⟩

theorem Program.graph_event_origin (index : Fin (p.events registers oracle).length) :
    p.Origin oracle ((p.graph registers oracle source co).event index) := by
  apply p.events_origin
  exact List.get_mem _ _

/-- A load receives exactly the oracle value at its actual thread/instruction position. -/
theorem Program.load_origin (h : occurrence ∈ p.events registers oracle)
    (hl : occurrence.effect.op = .load order) :
    ∃ (tid : Nat) (ht : tid < p.threads.length)
      (position : Nat) (hp : position < p.threads[tid].length) (destination : Nat),
      p.threads[tid][position] = .load order occurrence.effect.address destination ∧
      occurrence.thread = some tid ∧ occurrence.position = position ∧
      occurrence.effect.value = oracle tid position := by
  rcases p.events_origin h with ⟨address, ha, rfl⟩ | ⟨tid, ht, position, hp, rfl⟩
  · simp at hl
  · generalize hi : p.threads[tid][position] = instruction at *
    cases instruction with
    | load lo address destination =>
      simp only [Instr.effect, EventOp.load.injEq] at hl
      subst lo
      exact ⟨tid, ht, position, hp, destination, hi, rfl, rfl, rfl⟩
    | store so address value => simp [Instr.effect] at hl

/-- Store values are literal operands, independent of every oracle value. -/
theorem Program.store_origin (h : occurrence ∈ p.events registers oracle)
    (hs : occurrence.effect.op = .store order) :
    ∃ (tid : Nat) (ht : tid < p.threads.length)
      (position : Nat) (hp : position < p.threads[tid].length),
      p.threads[tid][position] = .store order occurrence.effect.address occurrence.effect.value ∧
      occurrence.thread = some tid ∧ occurrence.position = position := by
  rcases p.events_origin h with ⟨address, ha, rfl⟩ | ⟨tid, ht, position, hp, rfl⟩
  · simp at hs
  · generalize hi : p.threads[tid][position] = instruction at *
    cases instruction with
    | load lo address destination => simp [Instr.effect] at hs
    | store so address value =>
      simp only [Instr.effect, EventOp.store.injEq] at hs
      subst so
      exact ⟨tid, ht, position, hp, hi, rfl, rfl⟩

theorem Program.initial_origin (h : occurrence ∈ p.events registers oracle)
    (hi : occurrence.effect.op = .init) :
    ∃ (address : Nat) (ha : address < p.initial.length),
      occurrence = ⟨none, address, ⟨.init, address, p.initial[address]⟩⟩ := by
  rcases p.events_origin h with hi' | ⟨tid, ht, position, hp, rfl⟩
  · exact hi'
  · generalize hx : p.threads[tid][position] = instruction at hi
    cases instruction <;> simp [Instr.effect] at hi

/-- Ground values are initial arena words or actual immediate store operands. -/
def Program.GroundValue (p : Program) (value : Word) : Prop :=
  value ∈ p.initial ∨
    ∃ program ∈ p.threads, ∃ order address, Instr.store order address value ∈ program

theorem Program.write_grounded (h : occurrence ∈ p.events registers oracle)
    (hw : match occurrence.effect.op with | .store _ | .init => True | _ => False) :
    p.GroundValue occurrence.effect.value := by
  rcases p.events_origin h with ⟨address, ha, rfl⟩ | ⟨tid, ht, position, hp, rfl⟩
  · exact Or.inl (List.getElem_mem ha)
  · generalize hi : p.threads[tid][position] = instruction at *
    cases instruction with
    | load lo address destination => simp [Instr.effect] at hw
    | store so address value =>
      apply Or.inr
      refine ⟨p.threads[tid], List.getElem_mem ht, so, address, ?_⟩
      exact hi ▸ List.getElem_mem hp

/-- Compatible read sources cannot invent a value absent from initialization and literal stores. -/
theorem Program.no_invented_values
    (sources : (p.graph registers oracle source co).Sources)
    (read : (p.graph registers oracle source co).read index) :
    p.GroundValue ((p.graph registers oracle source co).event index).effect.value := by
  obtain ⟨hw, _, hv⟩ := sources.compatible index read
  rw [← hv]
  apply p.write_grounded
  · exact List.get_mem _ _
  · exact hw

/-- All materialized accesses, including initialization, are aligned and inside the arena. -/
theorem Program.access_safe
    (bounded : ∀ program ∈ p.threads, ∀ instruction ∈ program,
      instruction.address < p.initial.length)
    (h : occurrence ∈ p.events registers oracle) :
    AccessSafe p.initial.length occurrence.effect := by
  rcases p.events_origin h with ⟨address, ha, rfl⟩ | ⟨tid, ht, position, hp, rfl⟩
  · exact access_safe_of_index_lt _ ha
  · apply access_safe_of_index_lt
    have hb := bounded p.threads[tid] (List.getElem_mem ht)
      p.threads[tid][position] (List.getElem_mem hp)
    cases hi : p.threads[tid][position] <;> simpa [Instr.effect, Instr.address, hi] using hb

theorem Program.graph_access_safe
    (bounded : ∀ program ∈ p.threads, ∀ instruction ∈ program,
      instruction.address < p.initial.length)
    (index : Fin (p.events registers oracle).length) :
    AccessSafe p.initial.length ((p.graph registers oracle source co).event index).effect := by
  exact p.access_safe bounded (List.get_mem _ _)

theorem Program.admitted_access_safe (admitted : p.Admitted registers oracle source co)
    (index : Fin (p.events registers oracle).length) :
    AccessSafe p.initial.length ((p.graph registers oracle source co).event index).effect := by
  exact p.graph_access_safe admitted.1 index

end Ptx

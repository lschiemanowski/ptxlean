import PtxBinary32.ParallelHistory
import Ptx.SharedReductionMemory
import Ptx.CollectiveMemory

/-! Actual mixed-thread accesses, with disjoint global/shared location codes.
Barrier order is derived from the fetched history. Validity remains an explicit
memory-constraint check; it is not assumed by the candidate execution relation. -/
namespace Ptx.Scalar.Parallel.Memory
open Ptx.TraceMemory
namespace Prior
abbrev initial := Ptx.Scalar.SharedReduction.Machine.Memory.initial
abbrev initial_unique := Ptx.Scalar.SharedReduction.Machine.Memory.initial_unique
abbrev memoryKind := Ptx.Scalar.SharedReduction.Machine.Control.memoryKind
abbrev eval_effect_origin := Ptx.Scalar.SharedReduction.Machine.Control.eval_effect_origin
end Prior

def slot : Space → Fin 2
  | .global => 0 | .shared => 1

def location (space : Space) (address : Scalar.Address) : Location 2 :=
  ⟨slot space,address.toNat/4⟩

theorem spaces_distinct (a b : Scalar.Address) :
    (location .global a).code ≠ (location .shared b).code := by
  intro h
  have different := congrArg (fun l : Location 2 => l.storage.val) (Location.code_injective h)
  simp [location,slot] at different

def ofEffect (space : Space) (effect : MemoryEffect) : Access 2 :=
  ⟨location space effect.address,
    match effect.kind with | .load => .load .relaxed | .store => .store .relaxed,
    effect.value⟩

/-- The requested issuing thread, actual instruction fetch, executed predicate
and load/store direction must all match. This selects reviewed relaxed forms. -/
def access (program : List Instr) (thread : Nat) : Event n → Option (Access 2)
  | .scalar t (some space) occ =>
    match occ.memory with
    | none => none
    | some effect =>
      if t.val = thread ∧ program[occ.pc]? = some (.memory space occ.instruction) ∧
          occ.executed = true ∧ Prior.memoryKind occ.instruction.op = some effect.kind
      then some (ofEffect space effect) else none
  | _ => none

theorem access_origin (program : List Instr) (thread : Nat) (event : Event n) (a : Access 2)
    (emitted : access program thread event = some a) :
    ∃ t space occ effect,
      event = .scalar t (some space) occ ∧ t.val = thread ∧
      program[occ.pc]? = some (.memory space occ.instruction) ∧ occ.executed = true ∧
      occ.memory = some effect ∧ Prior.memoryKind occ.instruction.op = some effect.kind ∧
      a = ofEffect space effect := by
  cases event with
  | scalar t space occ =>
    cases space with
    | none => simp [access] at emitted
    | some space =>
      cases hm : occ.memory with
      | none => simp [access,hm] at emitted
      | some effect =>
        simp only [access,hm] at emitted
        split at emitted
        next h => exact ⟨t,space,occ,effect,rfl,h.1,h.2.1,h.2.2.1,hm,h.2.2.2,(Option.some.inj emitted).symm⟩
        next h => contradiction
  | _ => simp [access] at emitted

def labels (program : List Instr) (global shared : List Word) (events : List (Event n)) : List Ptx.Occurrence :=
  TraceMemory.events (Prior.initial global shared) (List.range n) (fun _ => events) (access program)

def graph (program : List Instr) (global shared : List Word) (events : List (Event n))
    (source : Fin (labels program global shared events).length → Fin (labels program global shared events).length)
    (co : Fin (labels program global shared events).length → Fin (labels program global shared events).length → Bool) :=
  TraceMemory.graph (labels program global shared events) source co

theorem labels_unique (program : List Instr) (global shared : List Word) (events : List (Event n)) :
    ((labels program global shared events).map identity).Nodup :=
  events_unique _ _ _ _ (Prior.initial_unique global shared) List.nodup_range

theorem labels_origin (program : List Instr) (global shared : List Word) (events : List (Event n))
    (event : Ptx.Occurrence) (member : event ∈ labels program global shared events) :
    (∃ i ∈ Prior.initial global shared, i.occurrence = event) ∨
    (∃ t, t < n ∧ ∃ p : Projected 2 (Event n),
      events[p.position]? = some p.origin ∧ access program t p.origin = some p.access ∧ p.occurrence t = event) := by
  simpa [labels,List.mem_range] using
    (events_member_iff (Prior.initial global shared) (List.range n) (fun _ => events) (access program) event).mp member

private theorem scalar_origin (s : State n) (selected : Fin n) (space : Option Space) (i : Scalar.Instr)
    (candidate : Option Word) (thread : Fin n) (seenSpace : Option Space) (occ : Scalar.Occurrence)
    (effect : MemoryEffect) (member : .scalar thread seenSpace occ ∈ (scalarStep candidate selected space i s).events)
    (memory : occ.memory = some effect) :
    thread=selected ∧ seenSpace=space ∧ occ.instruction=i ∧ occ.pc=(s.lanes selected).scalar.pc ∧
      occ.executed=true ∧ Prior.memoryKind i.op=some effect.kind := by
  cases h : Scalar.eval candidate i {(s.lanes selected).scalar with memory := arena s space} with
  | next next emitted =>
    have hm : thread=selected ∧ seenSpace=space ∧ occ=emitted := by
      cases space with
      | none => simpa only [scalarStep,h,List.mem_singleton,Event.scalar.injEq] using member
      | some space => cases space <;> simpa only [scalarStep,h,List.mem_singleton,Event.scalar.injEq] using member
    obtain ⟨rfl,rfl,rfl⟩ := hm
    exact ⟨rfl,rfl,Prior.eval_effect_origin candidate i
      {(s.lanes thread).scalar with memory := arena s seenSpace} next occ effect h memory⟩
  | halted next emitted =>
    have hm : thread=selected ∧ seenSpace=space ∧ occ=emitted := by
      simpa only [scalarStep,h,List.mem_singleton,Event.scalar.injEq] using member
    obtain ⟨rfl,rfl,rfl⟩ := hm
    rw [(Scalar.eval_halted h).2] at memory
    contradiction
  | fault reason => simp [scalarStep,h] at member
  | unsupported spelling => simp [scalarStep,h] at member

private theorem dispatch_access {s : State n} (step : Dispatch cfg candidate selected i s out)
    (fetch : program[(s.lanes selected).scalar.pc]? = some i)
    (member : .scalar thread (some space) occ ∈ out.events) (memory : occ.memory = some effect) :
    access program thread.val (.scalar thread (some space) occ) = some (ofEffect space effect) := by
  cases step with
  | localStep =>
    have origin := scalar_origin _ _ _ _ _ _ _ _ _ member memory
    cases origin.2.1
  | memory =>
    obtain ⟨rfl,spaceEq,instr,pc,executed,kind⟩ := scalar_origin _ _ _ _ _ _ _ _ _ member memory
    have eq := Option.some.inj spaceEq
    subst eq
    simp [access,memory,pc,instr,fetch,executed,kind]
  | binary32 _ => simp at member
  | exit => simp at member
  | sync =>
    rename_i resource
    cases hd : (Barrier.step (barrierConfig cfg s selected) s.barrier (barrierRequest cfg s selected resource)).disposition <;>
      simp [synchronize,hd] at member

/-- A fetched successful memory access cannot be omitted by the labeler. -/
theorem step_access_complete {s : State n} (step : Step cfg program candidate selected s out)
    (member : .scalar thread (some space) occ ∈ out.events) (memory : occ.memory = some effect) :
    access program thread.val (.scalar thread (some space) occ) = some (ofEffect space effect) := by
  have h := step.2
  split at h
  · subst out; simp at member
  · split at h
    · subst out; simp at member
    · split at h
      · subst out; simp at member
      · exact dispatch_access h (by assumption) member memory

theorem run_access_complete {s : State n} {events : List (Event n)} (run : Runs cfg program s events final)
    (member : .scalar thread (some space) occ ∈ events) (memory : occ.memory = some effect) :
    access program thread.val (.scalar thread (some space) occ) = some (ofEffect space effect) := by
  induction run with
  | nil => simp at member
  | cons step _ ih =>
    rcases List.mem_append.mp member with now | later
    · exact step_access_complete step now memory
    · exact ih later

/-- Original global byte addresses and shared byte addresses occupy distinct
catalogue slots. Initial events have no participant in collective ordering. -/
def owner (n : Nat) (e : Ptx.Occurrence) : Option (Fin n) :=
  e.thread.bind fun t => if h : t < n then some ⟨t,h⟩ else none

@[simp] theorem owner_program (t : Fin n) (position : Nat) (effect : Effect) :
    owner n ⟨some t.val,position,effect⟩ = some t := by simp [owner,t.isLt]

noncomputable def order {events : List (Event n)} (complete : History.CompleteOrigins events) (g : Graph k) :=
  History.certificate complete (fun i => owner n (g.event i)) (fun i => (g.event i).position)

/-- Single program writer per location is a structural lifetime obligation.
All competing initial writes precede it by the existing coherence rule. -/
theorem read_from_unique_writer {events : List (Event n)} (complete : History.CompleteOrigins events)
    (g : Graph k) (valid : Graph.Ordered.Valid g (order complete g).cross)
    (phase : History.Phase events) (w r : Fin k) (writer reader : Fin n)
    (wo : owner n (g.event w) = some writer) (ro : owner n (g.event r) = some reader)
    (before : (g.event w).position < History.arrivalPosition complete phase writer)
    (after : phase.position < (g.event r).position)
    (written : g.write w) (read : g.read r) (same : g.sameAddress w r)
    (unique : ∀ v, g.write v → g.sameAddress v r → ¬g.initial v → v=w) :
    g.source r=w ∧ (g.event r).effect.value=(g.event w).effect.value := by
  have latest : ∀ v, g.write v → g.sameAddress v r → v≠w → g.coherence v w := by
    intro v hv hs ne
    have init : g.initial v := by by_contra no; exact ne (unique v hv hs no)
    have sameWrite : g.sameAddress v w := hs.trans same.symm
    exact valid.co.initFirst v w init written sameWrite ne
  have wb := History.before_certificate complete (fun i => owner n (g.event i)) (fun i => (g.event i).position) w phase writer wo before
  have ra := History.after_certificate complete (fun i => owner n (g.event i)) (fun i => (g.event i).position) r phase reader ro after
  have source := CollectiveMemory.source_after_phase g (order complete g) valid w r phase
    (some writer) (some reader) wb ra written read same latest
  exact ⟨source,Graph.value_of_source g valid.sources w r read source⟩

/-- There are no untagged memory effects hidden in the local-instruction arm. -/
theorem run_memory_has_space {s : State n} {events : List (Event n)}
    (run : Runs cfg program s events final)
    (member : .scalar thread seenSpace occ ∈ events) (memory : occ.memory = some effect) :
    ∃ space, seenSpace = some space := by
  cases seenSpace with
  | none =>
    have safe := runs_access_safe run _ member
    have address := safe effect memory
    simp [arena,Scalar.ValidAddress] at address
  | some space => exact ⟨space,rfl⟩

/-- Every actual indexed memory occurrence has its exact label in the graph. -/
theorem run_graph_complete {s : State n} {events : List (Event n)}
    (run : Runs cfg program s events final) (source co)
    (position : Nat) (thread : Fin n) (space : Space) (occ : Scalar.Occurrence) (effect : MemoryEffect)
    (atIndex : events[position]? = some (.scalar thread (some space) occ))
    (memory : occ.memory = some effect) :
    ∃ r : Fin (labels program s.global s.shared events).length,
      (graph program s.global s.shared events source co).event r =
        ⟨some thread.val,position,(ofEffect space effect).effect⟩ := by
  have emitted := run_access_complete run (List.mem_of_getElem? atIndex) memory
  have member : (⟨some thread.val,position,(ofEffect space effect).effect⟩ : Ptx.Occurrence) ∈
      labels program s.global s.shared events := by
    apply (events_member_iff _ _ _ _ _).mpr
    exact .inr ⟨thread.val,List.mem_range.mpr thread.isLt,
      ⟨position,.scalar thread (some space) occ,ofEffect space effect⟩,atIndex,emitted,rfl⟩
  obtain ⟨r,bound,label⟩ := List.mem_iff_getElem.mp member
  exact ⟨⟨r,bound⟩,label⟩

/-- Source choices cannot invent a noninitial write: its value, address and
instruction are those of an actual store at the specified dynamic position. -/
theorem program_write_origin (program : List Instr) (global shared : List Word) (events : List (Event n))
    (source co) (w : Fin (labels program global shared events).length)
    (write : (graph program global shared events source co).write w)
    (noninitial : ¬(graph program global shared events source co).initial w) :
    ∃ thread position space occ effect,
      events[position]? = some (.scalar thread (some space) occ) ∧
      program[occ.pc]? = some (.memory space occ.instruction) ∧ occ.executed = true ∧
      occ.memory = some effect ∧ effect.kind = .store ∧
      (graph program global shared events source co).event w =
        ⟨some thread.val,position,(ofEffect space effect).effect⟩ := by
  have member : (graph program global shared events source co).event w ∈ labels program global shared events :=
    List.getElem_mem w.isLt
  rcases labels_origin program global shared events _ member with ⟨i,hi,he⟩ | ⟨t,ht,p,hp,ha,he⟩
  · exact False.elim (noninitial (by simp [Graph.initial,← he,Initial.occurrence]))
  · obtain ⟨thread,space,occ,effect,origin,threadEq,fetch,executed,memory,kind,value⟩ :=
      access_origin program t p.origin p.access ha
    have store : effect.kind = .store := by
      cases hk : effect.kind
      · simp [Graph.write,← he,Projected.occurrence,Access.effect,value,ofEffect,hk,AccessKind.op] at write
      · rfl
    refine ⟨thread,p.position,space,occ,effect,?_,fetch,executed,memory,store,?_⟩
    · simpa [origin] using hp
    · rw [← he]; simp [Projected.occurrence,value,threadEq]

/-- Barrier ordering used by an actual run, with no freely supplied phase facts. -/
noncomputable def runOrder {cfg : Config n} {s : State n} {events : List (Event n)}
    (run : Runs cfg program s events final) (reset : s.barrier = Barrier.reset generation)
    (source co) := order (History.completed_arrivals run reset) (graph program s.global s.shared events source co)

/-- For a single-writer scratch location, all valid read-source/coherence choices
force the producer's value across an observed completed round. The program still
has to prove the address, uniqueness and before/after timing obligations. -/
theorem run_read_from_unique_writer {cfg : Config n} {s : State n} {events : List (Event n)}
    (run : Runs cfg program s events final) (reset : s.barrier = Barrier.reset generation)
    (source co) (phase : History.Phase events)
    (w r : Fin (labels program s.global s.shared events).length) (writer reader : Fin n)
    (valid : Graph.Ordered.Valid (graph program s.global s.shared events source co) (runOrder run reset source co).cross)
    (wo : owner n ((graph program s.global s.shared events source co).event w) = some writer)
    (ro : owner n ((graph program s.global s.shared events source co).event r) = some reader)
    (before : ((graph program s.global s.shared events source co).event w).position <
      History.arrivalPosition (History.completed_arrivals run reset) phase writer)
    (after : phase.position < ((graph program s.global s.shared events source co).event r).position)
    (written : (graph program s.global s.shared events source co).write w)
    (read : (graph program s.global s.shared events source co).read r)
    (same : (graph program s.global s.shared events source co).sameAddress w r)
    (unique : ∀ v, (graph program s.global s.shared events source co).write v →
      (graph program s.global s.shared events source co).sameAddress v r →
      ¬(graph program s.global s.shared events source co).initial v → v=w) :
    (graph program s.global s.shared events source co).source r=w ∧
      ((graph program s.global s.shared events source co).event r).effect.value =
      ((graph program s.global s.shared events source co).event w).effect.value :=
  read_from_unique_writer (History.completed_arrivals run reset) _ valid phase w r writer reader wo ro
    before after written read same unique

end Ptx.Scalar.Parallel.Memory

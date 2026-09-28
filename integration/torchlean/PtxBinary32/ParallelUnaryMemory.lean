import PtxBinary32.ParallelUnary
import PtxBinary32.ParallelMemory
import Ptx.SharedReductionMemoryWitness

/-! Memory admission for parallel unary instructions. Labels project actual
fetched memory occurrences; arbitrary candidate reads remain unrestricted until
the unchanged whole-word memory constraints are checked. -/
namespace Ptx.Scalar.ParallelUnary.Memory
open Ptx.TraceMemory
noncomputable section
local instance : DecidableEq Instr := Classical.decEq _
variable {n : Nat} {program : List Instr} {global : List Word} {events : List (Event n)}
variable {s next final : State n} {event : Event n} {thread selected : Fin n}
variable {occ : Scalar.Occurrence} {effect : MemoryEffect} {e : Ptx.Occurrence}

abbrev initial (global : List Word) := SharedReduction.Machine.Memory.initial global []
abbrev ofEffect (effect : MemoryEffect) := Parallel.Memory.ofEffect .global effect
abbrev memoryKind := SharedReduction.Machine.Control.memoryKind

/-- Include only the issuing lane's actual executed fetched memory instruction. -/
def access (program : List Instr) (thread : Nat) : Event n → Option (Access 2)
  | .scalar t occ =>
    match occ.memory with
    | none => none
    | some effect =>
      if t.val=thread ∧ program[occ.pc]?=some (.scalar occ.instruction) ∧
          occ.executed=true ∧ memoryKind occ.instruction.op=some effect.kind
      then some (ofEffect effect) else none
  | _ => none

theorem access_origin (program : List Instr) (thread : Nat) (event : Event n) (a : Access 2)
    (emitted : access program thread event=some a) :
    ∃t occ effect, event=.scalar t occ ∧ t.val=thread ∧
      program[occ.pc]?=some (.scalar occ.instruction) ∧ occ.executed=true ∧
      occ.memory=some effect ∧ memoryKind occ.instruction.op=some effect.kind ∧ a=ofEffect effect := by
  cases event with
  | scalar t occ =>
    cases hm : occ.memory with
    | none => simp [access,hm] at emitted
    | some effect =>
      simp only [access,hm] at emitted
      split at emitted
      next h => exact ⟨t,occ,effect,rfl,h.1,h.2.1,h.2.2.1,hm,h.2.2.2,(Option.some.inj emitted).symm⟩
      next h => contradiction
  | _ => simp [access] at emitted

def labels (program : List Instr) (global : List Word) (events : List (Event n)) : List Ptx.Occurrence :=
  TraceMemory.events (initial global) (List.range n) (fun _ => events) (access program)

def graph (program : List Instr) (global : List Word) (events : List (Event n))
    (source : Fin (labels program global events).length → Fin (labels program global events).length)
    (co : Fin (labels program global events).length → Fin (labels program global events).length → Bool) :=
  TraceMemory.graph (labels program global events) source co

def Admitted (program : List Instr) (global : List Word) (events : List (Event n))
    (source : Fin (labels program global events).length → Fin (labels program global events).length)
    (co : Fin (labels program global events).length → Fin (labels program global events).length → Bool) : Prop :=
  Graph.Ordered.Valid (graph program global events source co) (fun _ _ => False)

theorem labels_unique (program : List Instr) (global : List Word) (events : List (Event n)) :
    ((labels program global events).map identity).Nodup :=
  events_unique _ _ _ _ (SharedReduction.Machine.Memory.initial_unique global []) List.nodup_range

theorem labels_origin (program : List Instr) (global : List Word) (events : List (Event n))
    (event : Ptx.Occurrence) (member : event∈labels program global events) :
    (∃i∈initial global, i.occurrence=event) ∨
    (∃t, t<n ∧ ∃p : Projected 2 (Event n), events[p.position]?=some p.origin ∧
      access program t p.origin=some p.access ∧ p.occurrence t=event) := by
  simpa [labels,List.mem_range] using
    (events_member_iff (initial global) (List.range n) (fun _ => events) (access program) event).mp member

/-- Future own-lane stores cannot serve a read. The same lemma includes
read-only locations, whose noninitial-writer case is empty. -/
theorem source_initial_of_future (g : Graph k) (extra : Fin k→Fin k→Prop)
    (valid : Graph.Ordered.Valid g extra) (r : Fin k) (read : g.read r)
    (future : ∀w, g.write w → ¬g.initial w → g.sameAddress w r → Graph.Ordered.cause g extra r w) :
    g.initial (g.source r) := by
  by_contra noninitial
  obtain ⟨write,same,_⟩ := valid.sources.compatible r read
  exact valid.no_future r (g.source r) read write same.symm
    (future _ write noninitial same) rfl

/-- No successful actual memory occurrence is omitted by the graph adapter. -/
theorem step_access_complete
    (step : Step target program candidate selected s next event)
    (seen : event=.scalar thread occ) (memory : occ.memory=some effect) :
    access program thread.val (.scalar thread occ)=some (ofEffect effect) := by
  obtain ⟨_,_,i,fetch,exec⟩ := step
  cases exec with
  | scalarNext eval =>
    cases seen
    obtain ⟨inst,pc,executed,kind⟩ := SharedReduction.Machine.Control.eval_effect_origin
      candidate _ _ _ _ _ eval memory
    simp [access,memory,pc,inst,fetch,executed,kind,input,memoryKind]
  | scalarHalted eval =>
    cases seen
    rw [(Scalar.eval_halted eval).2] at memory
    contradiction
  | binary _ | exponential _ | reciprocal _ => cases seen

theorem run_access_complete (run : Runs target program s events final)
    (member : .scalar thread occ∈events) (memory : occ.memory=some effect) :
    access program thread.val (.scalar thread occ)=some (ofEffect effect) := by
  induction run with
  | nil => simp at member
  | cons step _ ih =>
    rcases List.mem_cons.mp member with same | later
    · exact step_access_complete step same.symm memory
    · exact ih later

theorem run_graph_complete (run : Runs target program s events final) (source co)
    (position : Nat) (thread : Fin n) (occ : Scalar.Occurrence) (effect : MemoryEffect)
    (atIndex : events[position]?=some (.scalar thread occ)) (memory : occ.memory=some effect) :
    ∃r : Fin (labels program s.global events).length,
      (graph program s.global events source co).event r=
        ⟨some thread.val,position,(ofEffect effect).effect⟩ := by
  have emitted := run_access_complete run (List.mem_of_getElem? atIndex) memory
  have member : (⟨some thread.val,position,(ofEffect effect).effect⟩ : Ptx.Occurrence)∈
      labels program s.global events := by
    apply (events_member_iff _ _ _ _ _).mpr
    exact .inr ⟨thread.val,List.mem_range.mpr thread.isLt,
      ⟨position,.scalar thread occ,ofEffect effect⟩,atIndex,emitted,rfl⟩
  obtain ⟨r,bound,label⟩ := List.mem_iff_getElem.mp member
  exact ⟨⟨r,bound⟩,label⟩

/-- A noninitial graph writer is an actual fetched store, at its trace position. -/
theorem program_write_origin (program : List Instr) (global : List Word) (events : List (Event n))
    (source co) (w : Fin (labels program global events).length)
    (write : (graph program global events source co).write w)
    (noninitial : ¬(graph program global events source co).initial w) :
    ∃thread position occ effect,
      events[position]?=some (.scalar thread occ) ∧
      program[occ.pc]?=some (.scalar occ.instruction) ∧ occ.executed=true ∧
      occ.memory=some effect ∧ effect.kind=.store ∧
      (graph program global events source co).event w=
        ⟨some thread.val,position,(ofEffect effect).effect⟩ := by
  have member : (graph program global events source co).event w∈labels program global events := List.getElem_mem w.isLt
  rcases labels_origin program global events _ member with ⟨i,_,eq⟩ | ⟨t,_,p,hp,ha,eq⟩
  · exact False.elim (noninitial (by simp [Graph.initial,← eq,Initial.occurrence]))
  · obtain ⟨thread,occ,effect,origin,tid,fetch,executed,memory,_,value⟩ := access_origin program t p.origin p.access ha
    have store : effect.kind=.store := by
      cases hk : effect.kind
      · simp [Graph.write,← eq,Projected.occurrence,Access.effect,value,ofEffect,Parallel.Memory.ofEffect,hk,AccessKind.op] at write
      · rfl
    refine ⟨thread,p.position,occ,effect,?_,fetch,executed,memory,store,?_⟩
    · simpa [origin] using hp
    · rw [← eq]; simp [Projected.occurrence,value,tid]

theorem initial_origin (member : e∈labels program global events) (init : e.effect.op=.init) :
    ∃i∈initial global, e=i.occurrence := by
  rcases labels_origin program global events e member with ⟨i,hi,eq⟩ | ⟨t,_,p,_,ha,eq⟩
  · exact ⟨i,hi,eq.symm⟩
  · obtain ⟨_,_,effect,_,_,_,_,_,_,value⟩ := access_origin program t p.origin p.access ha
    cases hk : effect.kind <;>
      simp [← eq,Projected.occurrence,value,ofEffect,Parallel.Memory.ofEffect,Access.effect,AccessKind.op,hk] at init

/-- Once causal ownership excludes noninitial sources, admission determines the
actual original array value. The address is a location code, not a host read. -/
theorem initial_read_value (program : List Instr) (global : List Word) (events : List (Event n))
    (source co) (valid : Admitted program global events source co)
    (r : Fin (labels program global events).length) (index : Nat)
    (read : (graph program global events source co).read r)
    (address : ((graph program global events source co).event r).effect.address=(⟨0,index⟩ : Location 2).code)
    (future : ∀w, (graph program global events source co).write w →
      ¬(graph program global events source co).initial w →
      (graph program global events source co).sameAddress w r →
      Graph.Ordered.cause (graph program global events source co) (fun _ _ => False) r w) :
    ((graph program global events source co).event r).effect.value=global[index]! := by
  let g := graph program global events source co
  have init := source_initial_of_future g _ valid r read future
  obtain ⟨_,same,value⟩ := valid.sources.compatible r read
  obtain ⟨entry,inside,entryEq⟩ := initial_origin (List.getElem_mem (source r).isLt) init
  have location : entry.location=(⟨0,index⟩ : Location 2) := by
    apply Location.code_injective
    exact (congrArg (fun e : Ptx.Occurrence => e.effect.address) entryEq).symm.trans (same.trans address)
  obtain ⟨_,entryValue⟩ := SharedReduction.Machine.Memory.initial_global global [] entry index inside location
  change ((labels program global events)[(source r).val]).effect.value = _ at value
  rw [entryEq] at value
  simpa [Initial.occurrence,entryValue] using value.symm

end
end Ptx.Scalar.ParallelUnary.Memory

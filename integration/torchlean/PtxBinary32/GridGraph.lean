import PtxBinary32.GridAccessControl
import PtxBinary32.GridMemory
import Ptx.OrderedMemory

/-! One memory graph for the actual grid trace. Global initialization is shared;
each CTA's shared initialization has a distinct storage slot. Cross-barrier
edges cite actual arrival/completion occurrences of that same group. -/
namespace Ptx.Scalar.Parallel.Grid.Memory
open Ptx.TraceMemory (Access Initial Projected)

def threadId (g : Fin groups) (t : Fin n) : Nat := n*g.val+t.val

def owner : Grid.Event groups n → Option Nat
  | (g,.scalar t _ _) | (g,.binary32 t _) | (g,.exit t _) => some (threadId g t)
  | (g,.barrier (.arrival _ t)) => some (threadId g t)
  | (_, .barrier (.completion _)) => none

def ofEffect (g : Fin groups) (space : Space) (effect : MemoryEffect) : Access (groups+1) :=
  ⟨Grid.location g space effect.address,
    match effect.kind with | .load => .load .relaxed | .store => .store .relaxed,effect.value⟩

def access (program : List Instr) : Grid.Event groups n → Option (Access (groups+1))
  | (g,.scalar _ (some space) occ) =>
    match occ.memory with
    | none => none
    | some effect =>
      if program[occ.pc]?=some (.memory space occ.instruction) ∧ occ.executed=true ∧
          Parallel.Memory.Prior.memoryKind occ.instruction.op=some effect.kind
      then some (ofEffect g space effect) else none
  | _ => none

def initials (s : Grid.State groups n) : List (Initial (groups+1)) :=
  s.global.mapIdx (fun i value => ⟨⟨0,i⟩,value⟩) ++
    (List.finRange groups).flatMap (fun g => (s.blocks g).shared.mapIdx
      (fun i value => ⟨⟨⟨g.val+1,by omega⟩,i⟩,value⟩))

def label (p : Projected (groups+1) (Grid.Event groups n)) : Ptx.Occurrence :=
  ⟨owner p.origin,p.position,p.access.effect⟩

def labels (program : List Instr) (s : Grid.State groups n) (events : List (Grid.Event groups n)) : List Ptx.Occurrence :=
  (initials s).map Initial.occurrence ++ (Ptx.TraceMemory.project (access program) events).map label

def graph (program : List Instr) (s : Grid.State groups n) (events : List (Grid.Event groups n))
    (source : Fin (labels program s events).length → Fin (labels program s events).length)
    (co : Fin (labels program s events).length → Fin (labels program s events).length → Bool) :
    Graph (labels program s events).length := Ptx.TraceMemory.graph (labels program s events) source co

/-- Every cross edge stays within one actually completed group barrier. -/
def cross (program : List Instr) (s : Grid.State groups n) (events : List (Grid.Event groups n))
    (a b : Fin (labels program s events).length) : Prop :=
  ∃ (g : Fin groups) (writer reader : Fin n) (key : Barrier.Key) (arrival completion : Nat),
    events[arrival]?=some (g,.barrier (.arrival key writer)) ∧
    events[completion]?=some (g,.barrier (.completion key)) ∧
    arrival<completion ∧
    (labels program s events)[a].thread=some (threadId g writer) ∧
    (labels program s events)[b].thread=some (threadId g reader) ∧
    (labels program s events)[a].position<arrival ∧ completion<(labels program s events)[b].position

def Admitted (program : List Instr) (s : Grid.State groups n) (events : List (Grid.Event groups n)) : Prop :=
  ∃ source co, Graph.Ordered.Valid (graph program s events source co) (cross program s events)

theorem access_complete {s final : Grid.State groups n} {events : List (Grid.Event groups n)}
    (run : Grid.Runs cfg program s events final) (g : Fin groups) (t : Fin n) (space : Space)
    (occ : Scalar.Occurrence) (effect : MemoryEffect)
    (member : (g,.scalar t (some space) occ) ∈ events) (memory : occ.memory=some effect) :
    access program (g,.scalar t (some space) occ)=some (ofEffect g space effect) := by
  have origin := Grid.run_memory_origin run g t space occ effect member memory
  simp [access,memory,origin.1,origin.2.1,origin.2.2]

theorem graph_complete {s final : Grid.State groups n} {events : List (Grid.Event groups n)}
    (run : Grid.Runs cfg program s events final) (source co) (p : Nat)
    (g : Fin groups) (t : Fin n) (space : Space) (occ : Scalar.Occurrence) (effect : MemoryEffect)
    (atP : events[p]?=some (g,.scalar t (some space) occ)) (memory : occ.memory=some effect) :
    ∃ r : Fin (labels program s events).length,
      (graph program s events source co).event r=⟨some (threadId g t),p,(ofEffect g space effect).effect⟩ := by
  have emitted := access_complete run g t space occ effect (List.mem_of_getElem? atP) memory
  have projected := Ptx.TraceMemory.project_complete (access program) events atP emitted
  have member : (⟨some (threadId g t),p,(ofEffect g space effect).effect⟩ : Ptx.Occurrence) ∈ labels program s events := by
    apply List.mem_append_right
    exact List.mem_map.mpr ⟨_,projected,rfl⟩
  obtain ⟨i,hi,eq⟩ := List.mem_iff_getElem.mp member
  exact ⟨⟨i,hi⟩,eq⟩

theorem threadId_unique (g h : Fin groups) (t u : Fin n)
    (same : threadId g t=threadId h u) : g=h ∧ t=u := by
  have tn := t.isLt
  have un := u.isLt
  have positive : 0<n := by omega
  have dg := congrArg (·/n) same
  have dt := congrArg (·%n) same
  simp [threadId,Nat.mul_add_div positive,Nat.div_eq_of_lt tn,Nat.div_eq_of_lt un] at dg
  simp [threadId,Nat.add_mod,Nat.mod_eq_of_lt tn,Nat.mod_eq_of_lt un] at dt
  exact ⟨Fin.ext dg,Fin.ext dt⟩

theorem cross_forward (program : List Instr) (s : Grid.State groups n) (events : List (Grid.Event groups n))
    (a b : Fin (labels program s events).length) (edge : cross program s events a b) :
    (labels program s events)[a].position<(labels program s events)[b].position := by
  obtain ⟨g,w,r,key,arrival,completion,_,_,order,_,_,before,after⟩ := edge
  omega

end Ptx.Scalar.Parallel.Grid.Memory

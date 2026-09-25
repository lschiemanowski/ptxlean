import PtxBinary32.ParallelReference
import PtxBinary32.ParallelMemory
import Ptx.SharedReductionMemoryWitness
import Mathlib.Tactic.FinCases

/-! A two-thread computed-publication witness across two reused barrier phases.
Both threads load distinct inputs, publish them, add the peer's value, publish
into fresh scratch, and copy the peer's computed result to distinct outputs.
This exercises the mixed machine and memory admission; it is not a dense layer. -/
namespace Ptx.Scalar.Parallel.Publication

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def config : Config 2 := ⟨⟨94,70⟩,0,by decide⟩

def program : List Instr := [
  .memory .global (.plain (.load 0 (.reg 0))),
  .memory .shared (.plain (.store (.reg 0) (.reg 0))),
  .sync 0,
  .memory .shared (.plain (.load 1 (.reg 1))),
  .binary32 ⟨.always,.add,2,.reg 0,.reg 1⟩,
  .memory .shared (.plain (.store (.reg 2) (.reg 2))),
  .sync 0,
  .memory .shared (.plain (.load 3 (.reg 3))),
  .memory .global (.plain (.store (.reg 2) (.reg 3))),
  .exit]

def initial (a b : Word) : State 2 :=
  ⟨fun t => ⟨⟨0,fun _ => 0,
    fun r => match r with
      | 0 => BitVec.ofNat 64 (4*t.val)
      | 1 => BitVec.ofNat 64 (4*(1-t.val))
      | 2 => BitVec.ofNat 64 (4*(2+t.val))
      | 3 => BitVec.ofNat 64 (4*(3-t.val))
      | _ => 0,
    fun _ => false,[]⟩,false⟩,
    [a,b,0,0],[0,0,0,0],Barrier.reset 0,none⟩

/-- Scheduling by instruction keeps the example short. The machine itself has
no lockstep scheduling requirement. -/
def schedule : List (Fin 2) := List.replicate 10 [0,1] |>.flatten

def execution (a b : Word) := Reference.run config program (initial a b) schedule

theorem execution_sound (a b : Word) :
    Runs config program (initial a b) (execution a b).2.1 (execution a b).1 :=
  Reference.run_sound _ _ _ _ (by constructor <;> decide)

theorem completed (a b : Word) :
    (∀ t, ((execution a b).1.lanes t).halted = true) ∧
    (execution a b).1.barrier = Barrier.reset 2 ∧
    (execution a b).1.global = [a,b,Ptx.Binary32.reference .add b a,Ptx.Binary32.reference .add a b] ∧
    (execution a b).1.shared = [a,b,Ptx.Binary32.reference .add a b,Ptx.Binary32.reference .add b a] := by
  simp (config := {maxSteps := 100000}) [execution, Reference.run, schedule,
    Reference.step, Reference.dispatch, Reference.binary32, program, initial,
    scalarStep, Scalar.eval, setLane, arena, Scalar.Instr.plain, Scalar.Guard.eval,
    Scalar.Operand64.eval, Scalar.Operand32.eval, Scalar.update, Function.update,
    Scalar.addressIndex, synchronize, barrierConfig, barrierRequest, config,
    Barrier.step, Barrier.key, Barrier.reset, Barrier.mark, Barrier.Complete,
    Barrier.Waiting, Fin.forall_fin_two]

theorem successful (a b : Word) :
    (execution a b).2.2 = [.advanced,.advanced,.advanced,.advanced,.waiting,.released,
      .advanced,.advanced,.advanced,.advanced,.advanced,.advanced,.waiting,.released,
      .advanced,.advanced,.advanced,.advanced,.halted,.halted] := by
  simp (config := {maxSteps := 100000}) [execution, Reference.run, schedule,
    Reference.step, Reference.dispatch, Reference.binary32, program, initial,
    scalarStep, Scalar.eval, setLane, arena, Scalar.Instr.plain, Scalar.Guard.eval,
    Scalar.Operand64.eval, Scalar.Operand32.eval, Scalar.update, Function.update,
    Scalar.addressIndex, synchronize, barrierConfig, barrierRequest, config,
    Barrier.step, Barrier.key, Barrier.reset, Barrier.mark, Barrier.Complete,
    Barrier.Waiting, Fin.forall_fin_two]

/-- A small presentation of the actual projected labels, checked against the
runner below. Initial positions are location codes; program positions are
indices in the complete execution, including its non-memory events. -/
def labels (a b : Word) : List Ptx.Occurrence := [
  ⟨none,0,⟨.init,0,a⟩⟩, ⟨none,2,⟨.init,2,b⟩⟩,
  ⟨none,4,⟨.init,4,0⟩⟩, ⟨none,6,⟨.init,6,0⟩⟩,
  ⟨none,1,⟨.init,1,0⟩⟩, ⟨none,3,⟨.init,3,0⟩⟩,
  ⟨none,5,⟨.init,5,0⟩⟩, ⟨none,7,⟨.init,7,0⟩⟩,
  ⟨some 0,0,⟨.load .relaxed,0,a⟩⟩,
  ⟨some 0,2,⟨.store .relaxed,1,a⟩⟩,
  ⟨some 0,7,⟨.load .relaxed,3,b⟩⟩,
  ⟨some 0,11,⟨.store .relaxed,5,Ptx.Binary32.reference .add a b⟩⟩,
  ⟨some 0,16,⟨.load .relaxed,7,Ptx.Binary32.reference .add b a⟩⟩,
  ⟨some 0,18,⟨.store .relaxed,4,Ptx.Binary32.reference .add b a⟩⟩,
  ⟨some 1,1,⟨.load .relaxed,2,b⟩⟩,
  ⟨some 1,3,⟨.store .relaxed,3,b⟩⟩,
  ⟨some 1,8,⟨.load .relaxed,1,a⟩⟩,
  ⟨some 1,12,⟨.store .relaxed,7,Ptx.Binary32.reference .add b a⟩⟩,
  ⟨some 1,17,⟨.load .relaxed,5,Ptx.Binary32.reference .add a b⟩⟩,
  ⟨some 1,19,⟨.store .relaxed,6,Ptx.Binary32.reference .add a b⟩⟩]

theorem labels_actual (a b : Word) :
    Memory.labels program (initial a b).global (initial a b).shared (execution a b).2.1 = labels a b := by
  simp (config := {maxSteps := 100000}) [execution, Reference.run, schedule,
    Reference.step, Reference.dispatch, Reference.binary32, program, initial,
    scalarStep, Scalar.eval, setLane, arena, Scalar.Instr.plain, Scalar.Guard.eval,
    Scalar.Operand64.eval, Scalar.Operand32.eval, Scalar.update, Function.update,
    Scalar.addressIndex, synchronize, barrierConfig, barrierRequest, config,
    Barrier.step, Barrier.key, Barrier.reset, Barrier.mark, Barrier.Complete,
    Barrier.Waiting, Fin.forall_fin_two,
    Memory.labels, Memory.Prior.initial, SharedReduction.Machine.Memory.initial, List.range_succ, TraceMemory.events, TraceMemory.project,
    TraceMemory.label, TraceMemory.Initial.occurrence, TraceMemory.Projected.occurrence,
    TraceMemory.Access.effect, TraceMemory.AccessKind.op, TraceMemory.Location.code,
    Memory.access, Memory.ofEffect, Memory.location, Memory.slot,
    Memory.Prior.memoryKind, SharedReduction.Machine.Control.memoryKind, Scalar.occurrence, Scalar.Binary32.occurrence, labels]

def source : Fin 20 → Fin 20 := fun i => match i.val with
  | 8 => 0 | 10 => 15 | 12 => 17 | 14 => 1 | 16 => 9 | 18 => 11 | _ => i

def rank : Fin 20 → Nat := ![0,1,2,3,4,5,6,7,8,10,15,19,24,26,9,11,16,20,25,27]

def coherent : Fin 20 → Fin 20 → Bool := fun i j =>
  (i.val == 2 && j.val == 13) || (i.val == 3 && j.val == 19) ||
  (i.val == 4 && j.val == 9) || (i.val == 5 && j.val == 15) ||
  (i.val == 6 && j.val == 11) || (i.val == 7 && j.val == 17)

def graph (a b : Word) : Graph 20 := ⟨fun i => (labels a b)[i.val]'(by have := i.isLt; simp [labels]), source,coherent⟩

noncomputable def order (a b : Word) :=
  Memory.order (History.completed_arrivals (execution_sound a b) rfl) (graph a b)

private theorem rank_injective : Function.Injective rank := by decide

private theorem sources (a b : Word) : (graph a b).Sources := by
  constructor
  intro r
  fin_cases r <;> simp [graph,labels,source,Graph.read,Graph.write,Graph.sameAddress]

private theorem chronological (a b : Word) (i j : Fin 20)
    (hi : ((graph a b).event i).thread ≠ none)
    (hj : ((graph a b).event j).thread ≠ none)
    (h : ((graph a b).event i).position < ((graph a b).event j).position) : rank i < rank j := by
  have ri : rank i = 8 + ((graph a b).event i).position := by
    fin_cases i <;> simp_all [graph,labels,rank]
  have rj : rank j = 8 + ((graph a b).event j).position := by
    fin_cases j <;> simp_all [graph,labels,rank]
  omega

private theorem no_release (a b : Word) (i : Fin 20) : ¬(graph a b).release i := by
  fin_cases i <;> simp [graph,labels,Graph.release]

private theorem cross_before (a b : Word) (i j : Fin 20) (h : (order a b).cross i j) : rank i < rank j := by
  have pos := (order a b).cross_increases h
  change 3 * ((graph a b).event i).position < 3 * ((graph a b).event j).position at pos
  obtain ⟨phase,ti,tj,hi,hj⟩ := h
  have oi : ((graph a b).event i).thread ≠ none := by
    intro no
    have := hi.1
    have someThread := hi.2.1
    change ti.isSome at someThread
    change Memory.owner 2 ((graph a b).event i) = ti at this
    simp [Memory.owner,no] at this
    simp [← this] at someThread
  have oj : ((graph a b).event j).thread ≠ none := by
    intro no
    have := hj.1
    have someThread := hj.2.1
    change tj.isSome at someThread
    change Memory.owner 2 ((graph a b).event j) = tj at this
    simp [Memory.owner,no] at this
    simp [← this] at someThread
  exact chronological a b i j oi oj (by omega)

/-- All local obligations, including actual read values, are discharged for the
trace. Collective order is derived from that trace's completed barriers. -/
theorem serial_certificate (a b : Word) :
    SharedReduction.Machine.Memory.SerialCertificate (graph a b) (order a b).cross rank where
  injective := rank_injective
  sources := sources a b
  source_before := by
    intro r
    fin_cases r <;> simp [graph, labels, source, rank, Graph.read]
  latest := by
    intro w r
    fin_cases w <;> fin_cases r <;> simp [graph, labels, source, rank, Graph.read, Graph.write, Graph.sameAddress]
  coherence_iff := by
    intro i j
    fin_cases i <;> fin_cases j <;> simp [graph, labels, rank, coherent, Graph.write, Graph.sameAddress, Graph.coherence]
  initial_before := by
    intro i w
    fin_cases i <;> fin_cases w <;> simp [graph, labels, rank, Graph.write, Graph.sameAddress, Graph.initial]
  base_before := by
    intro i j h
    rcases h with (po | sync) | cross
    · exact chronological a b i j po.1 (by rw [← po.2.1]; exact po.1) po.2.2
    · obtain ⟨_,w,r,pattern,_⟩ := sync
      rcases pattern with ⟨_,release⟩ | ⟨release,_⟩ <;> exact False.elim (no_release a b i release)
    · exact cross_before a b i j cross

theorem admitted (a b : Word) : Graph.Ordered.Valid (graph a b) (order a b).cross :=
  (serial_certificate a b).valid

theorem grounded (a b : Word) (i : Fin 20) :
    ¬Path (SharedReduction.Machine.Memory.grounding (graph a b) (order a b).cross) i i :=
  (serial_certificate a b).grounded i

/-- Every graph label is the corresponding label of the actual execution. -/
theorem graph_actual (a b : Word) : List.ofFn (graph a b).event =
    Memory.labels program (initial a b).global (initial a b).shared (execution a b).2.1 := by
  rw [labels_actual]
  rfl

/-- A completed, admitted and grounded execution exists for every pair of input
words, including exceptional encodings. This does not claim real-valued accuracy
for exceptional inputs or fairness of arbitrary hardware schedules. -/
theorem admitted_execution (a b : Word) :
    ∃ final events,
      Runs config program (initial a b) events final ∧
      (∀ t, (final.lanes t).halted = true) ∧
      final.global = [a,b,Ptx.Binary32.reference .add b a,Ptx.Binary32.reference .add a b] ∧
      Memory.labels program (initial a b).global (initial a b).shared events = List.ofFn (graph a b).event ∧
      Graph.Ordered.Valid (graph a b) (order a b).cross := by
  exact ⟨_,_,execution_sound a b,(completed a b).1,(completed a b).2.2.1,(graph_actual a b).symm,admitted a b⟩

theorem memory_safe (a b : Word) (event : Event 2) (member : event ∈ (execution a b).2.1) :
    AccessSafe (initial a b) event := runs_access_safe (execution_sound a b) event member

end Ptx.Scalar.Parallel.Publication

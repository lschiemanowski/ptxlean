import PoissonPTX.ControlFlowObserved
import PoissonPTX.ConcurrentOrder

/-! One concurrent fetched machine for ordinary control flow and full-block
barriers. Counter positions are actual instruction-list indices. Loads choose
candidate words; memory-source admission is a separate predicate on the actual
event history. There are no implicit phase barriers or supplied local runs. -/
namespace PtxTorchLean.Poisson.PTX.Concurrent.NativeFlow

inductive Instr where
  | flow (instruction : Flow.Instr)
  | sync (resource : Fin 16)
  deriving DecidableEq, Repr

structure State (n : Nat) where
  core : Concurrent.State n
  predicates : Fin n → Nat → Bool
  halted : Fin n → Bool

def lane (s : State n) (thread : Fin n) : Flow.State :=
  ⟨s.core.lanes thread,s.predicates thread,s.halted thread⟩

def update (s : State n) (thread : Fin n) (next : Flow.State) : State n :=
  ⟨setLane s.core thread next.core,Function.update s.predicates thread next.predicates,
    Function.update s.halted thread next.halted⟩

structure Outcome (n : Nat) where
  state : State n
  events : List (Event n)
  indices : List (Fin n × IndexSources.Access)

inductive Step (cfg : Config n) (ctx : Fin n → Kernel.Context) (program : List Instr)
    (thread : Fin n) : State n → Outcome n → Prop where
  | flow (running : s.halted thread=false) (fresh : s.core.barrier.arrived thread=false)
      (fetch : program[(s.core.lanes thread).pc]?=some (.flow instruction))
      (actual : Flow.Observed.Eval (ctx thread) instruction (lane s thread) next access index) :
      Step cfg ctx program thread s
        ⟨update s thread next,access.toList.map (Event.data thread),index.toList.map (thread,·)⟩
  | sync (running : s.halted thread=false) (fresh : s.core.barrier.arrived thread=false)
      (fetch : program[(s.core.lanes thread).pc]?=some (.sync resource)) :
      Step cfg ctx program thread s
        ⟨{s with core:=(synchronize cfg s.core thread resource).state},
          (synchronize cfg s.core thread resource).events,[]⟩

inductive Runs (cfg : Config n) (ctx : Fin n → Kernel.Context) (program : List Instr) :
    State n → List (Event n) → List (Fin n × IndexSources.Access) → State n → Prop where
  | nil : Runs cfg ctx program s [] [] s
  | cons : Step cfg ctx program thread s out → Runs cfg ctx program out.state rest indices final →
      Runs cfg ctx program s (out.events++rest) (out.indices++indices) final

theorem waiting_blocks (waiting : s.core.barrier.arrived thread=true) :
    ¬Step cfg ctx program thread s out := by intro step; cases step <;> simp_all

theorem halted_blocks (halted : s.halted thread=true) :
    ¬Step cfg ctx program thread s out := by intro step; cases step <;> simp_all

theorem step_aligned (actual : Step cfg ctx program thread s out) (aligned : Aligned s.core) :
    Aligned out.state.core := by
  cases actual with
  | flow running fresh fetch step => exact setLane_aligned aligned fresh _
  | sync => exact synchronize_aligned _ _ _ _ aligned

theorem aligned (run : Runs cfg ctx program s events indices t) (initial : Aligned s.core) :
    Aligned t.core := by
  induction run with
  | nil => exact initial
  | cons one rest ih => exact ih (step_aligned one initial)

theorem append (first : Runs cfg ctx program s a ia middle)
    (second : Runs cfg ctx program middle b ib final) :
    Runs cfg ctx program s (a++b) (ia++ib) final := by
  induction first with
  | nil => exact second
  | cons one rest ih => simpa [List.append_assoc] using Runs.cons one (ih second)

theorem lane_update_self (s : State n) (thread : Fin n) (next : Flow.State) : lane (update s thread next) thread=next := by
  cases next; simp [lane,update,setLane]

theorem lane_update_other (s : State n) (thread owner : Fin n) (different : owner≠thread) (next : Flow.State) :
    lane (update s thread next) owner=lane s owner := by simp [lane,update,setLane,Function.update,different]

end PtxTorchLean.Poisson.PTX.Concurrent.NativeFlow

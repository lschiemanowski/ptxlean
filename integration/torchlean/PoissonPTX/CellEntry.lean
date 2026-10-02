import PoissonPTX.IndexedCandidate
import PoissonPTX.CellGatherTensor
import PoissonPTX.CellPrologueEntry
import PoissonPTX.ConcurrentCut

namespace PtxTorchLean.Poisson.PTX.CellEntry

/-- The whole prefix through the first full-block barrier. Instruction counters
are the emitted counters: setup 0--6, guard 7, gather 8--19, barrier 20. -/
inductive Instr where
  | setup (op : CellPrologue.Instr)
  | gather (op : Indexed.Instr)
  | skip (target : Nat)
  | sync
  deriving DecidableEq, Repr

def program (width : Nat) (cells source : Word) : List Instr :=
  (CellPrologue.program width).map .setup ++ [.skip 20] ++
    (CellGather.code width cells source).map .gather ++ [.sync]

structure State (n : Nat) where
  core : Concurrent.State n
  live : Fin n → Bool

structure Outcome (n : Nat) where
  state : State n
  events : List (Concurrent.Event n)
  indices : List (Fin n × IndexSources.Access)

def lane (s : State n) (thread : Fin n) : CellPrologue.State :=
  ⟨s.core.lanes thread,s.live thread⟩

def setLane (s : State n) (thread : Fin n) (next : CellPrologue.State) : State n :=
  ⟨Concurrent.setLane s.core thread next.core,Function.update s.live thread next.live⟩

def synchronize (cfg : Concurrent.Config n) (s : State n) (thread : Fin n) : Outcome n :=
  let out := Concurrent.synchronize cfg s.core thread 0
  ⟨⟨out.state,s.live⟩,out.events,[]⟩

inductive Dispatch (cfg : Concurrent.Config n) (ctx : Fin n → CellPrologue.Context) (thread : Fin n) :
    Instr → State n → Outcome n → Prop
  | setup (step : CellPrologue.eval (ctx thread) op (lane s thread)=some next) :
      Dispatch cfg ctx thread (.setup op) s ⟨setLane s thread next,[],[]⟩
  | gather (step : Indexed.Candidate.Data op (s.core.lanes thread) next access index) :
      Dispatch cfg ctx thread (.gather op) s
        ⟨⟨Concurrent.setLane s.core thread next,s.live⟩,
          access.toList.map (Concurrent.Event.data thread),index.toList.map (thread,·)⟩
  | skip : Dispatch cfg ctx thread (.skip target) s
      ⟨⟨Concurrent.setLane s.core thread {s.core.lanes thread with
          pc:=if s.live thread then (s.core.lanes thread).pc+1 else target},s.live⟩,[],[]⟩
  | sync : Dispatch cfg ctx thread .sync s (synchronize cfg s thread)

def Step (cfg : Concurrent.Config n) (ctx : Fin n → CellPrologue.Context)
    (code : List Instr) (thread : Fin n) (s : State n) (out : Outcome n) : Prop :=
  s.core.barrier.arrived thread=false ∧
  ∃ i, code[(s.core.lanes thread).pc]?=some i ∧ Dispatch cfg ctx thread i s out

inductive Runs (cfg : Concurrent.Config n) (ctx : Fin n → CellPrologue.Context)
    (code : List Instr) : State n → List (Concurrent.Event n) → List (Fin n × IndexSources.Access) → State n → Prop
  | nil : Runs cfg ctx code s [] [] s
  | cons : Step cfg ctx code thread s out → Runs cfg ctx code out.state words indices final →
      Runs cfg ctx code s (out.events++words) (out.indices++indices) final

theorem program_length : (program width cells source).length=21 := by
  simp [program,CellPrologue.program,CellGather.code]

theorem barrier_fetch : (program width cells source)[20]?=some .sync := by
  simp [program,CellPrologue.program,CellGather.code]

theorem step_aligned (step : Step cfg ctx code thread s out) (aligned : Concurrent.Aligned s.core) :
    Concurrent.Aligned out.state.core := by
  obtain ⟨fresh,i,fetch,dispatch⟩ := step
  cases dispatch with
  | setup => exact Concurrent.setLane_aligned aligned fresh _
  | gather => exact Concurrent.setLane_aligned aligned fresh _
  | skip => exact Concurrent.setLane_aligned aligned fresh _
  | sync => exact Concurrent.synchronize_aligned _ _ _ _ aligned

theorem runs_aligned (run : Runs cfg ctx code s events indices final) (aligned : Concurrent.Aligned s.core) :
    Concurrent.Aligned final.core := by
  induction run with
  | nil => exact aligned
  | cons step _ ih => exact ih (step_aligned step aligned)

theorem waiting_blocks (waiting : s.core.barrier.arrived thread=true) :
    ¬Step cfg ctx code thread s out := by
  intro h
  have := h.1
  simp_all

end PtxTorchLean.Poisson.PTX.CellEntry

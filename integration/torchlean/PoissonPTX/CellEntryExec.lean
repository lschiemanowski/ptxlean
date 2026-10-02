import PoissonPTX.CellEntryBarrier
import PoissonPTX.CellEntryResult
import PoissonPTX.ConcurrentExec

namespace PtxTorchLean.Poisson.PTX.Indexed.Candidate

def evaluate (i : Instr) (s : State) (word : Word) :
    Option (State × Option Concurrent.Access × Option IndexSources.Access) :=
  match i with
  | .data op => (Concurrent.evaluate op s word).map fun (t,a) => (t,a,none)
  | .mad32 dst a scale b => some (assign s dst (mad s a scale b),none,none)
  | .wide4 dst src => some (assign s dst (wide s src),none,none)
  | .load32 dst addr => if Valid32 s.globalStart s.globalBytes (s.regs addr).toNat then
      some (assign s dst ((Kernel.u32 word).setWidth 64),none,some ⟨s.pc,(s.regs addr).toNat,Kernel.u32 word⟩)
    else none

theorem evaluate_sound (executed : evaluate i s word=some (t,a,index)) : Data i s t a index := by
  cases i with
  | data op =>
    simp only [evaluate,Option.map_eq_some_iff] at executed
    obtain ⟨⟨next,access⟩,step,equal⟩ := executed
    cases equal
    exact .data (Concurrent.evaluate_sound step)
  | mad32 => cases executed; exact .mad32
  | wide4 => cases executed; exact .wide4
  | load32 =>
    simp only [evaluate] at executed
    split at executed
    · cases Option.some.inj executed; exact .load32 (by assumption)
    · simp at executed

end PtxTorchLean.Poisson.PTX.Indexed.Candidate

namespace PtxTorchLean.Poisson.PTX.CellEntry

/-- Chosen values are explicit. A successful candidate interpreter run does
not by itself establish compatibility of those values with memory sources. -/
def tick (cfg : Concurrent.Config n) (ctx : Fin n → CellPrologue.Context) (code : List Instr)
    (choose : Fin n → PTX.State → Word) (thread : Fin n) (s : State n) : Option (Outcome n) := do
  if s.core.barrier.arrived thread then none else do
    match ← code[(s.core.lanes thread).pc]? with
    | .setup op =>
      let next ← CellPrologue.eval (ctx thread) op (lane s thread)
      return ⟨setLane s thread next,[],[]⟩
    | .gather op =>
      let (next,access,index) ← Indexed.Candidate.evaluate op (s.core.lanes thread) (choose thread (s.core.lanes thread))
      return ⟨⟨Concurrent.setLane s.core thread next,s.live⟩,
        access.toList.map (Concurrent.Event.data thread),index.toList.map (thread,·)⟩
    | .skip target => return ⟨⟨Concurrent.setLane s.core thread
        {s.core.lanes thread with pc:=if s.live thread then (s.core.lanes thread).pc+1 else target},s.live⟩,[],[]⟩
    | .sync => return synchronize cfg s thread

theorem tick_sound (executed : tick cfg ctx code choose thread s=some out) :
    Step cfg ctx code thread s out := by
  unfold tick at executed
  split at executed
  · simp at executed
  · have fresh : s.core.barrier.arrived thread=false := by simpa using ‹¬s.core.barrier.arrived thread=true›
    cases fetch : code[(s.core.lanes thread).pc]? with
    | none => simp [fetch] at executed
    | some i =>
      refine ⟨fresh,i,fetch,?_⟩
      cases i with
      | setup op =>
        cases step : CellPrologue.eval (ctx thread) op (lane s thread) with
        | none => simp [fetch,step] at executed
        | some next => simp [fetch,step] at executed; subst out; exact .setup step
      | gather op =>
        cases step : Indexed.Candidate.evaluate op (s.core.lanes thread) (choose thread (s.core.lanes thread)) with
        | none => simp [fetch,step] at executed
        | some triple =>
          rcases triple with ⟨next,access,index⟩
          simp [fetch,step] at executed
          subst out
          exact .gather (Indexed.Candidate.evaluate_sound step)
      | skip target => simp [fetch] at executed; subst out; exact .skip
      | sync => simp [fetch] at executed; subst out; exact .sync

def execute (cfg : Concurrent.Config n) (ctx : Fin n → CellPrologue.Context) (code : List Instr)
    (choose : Fin n → PTX.State → Word) : List (Fin n) → State n → Option (Outcome n)
  | [],s => some ⟨s,[],[]⟩
  | t::rest,s => do
    let first ← tick cfg ctx code choose t s
    let last ← execute cfg ctx code choose rest first.state
    return ⟨last.state,first.events++last.events,first.indices++last.indices⟩

theorem execute_sound (executed : execute cfg ctx code choose schedule s=some out) :
    Runs cfg ctx code s out.events out.indices out.state := by
  induction schedule generalizing s out with
  | nil => simp only [execute,Option.some.injEq] at executed; subst out; exact .nil
  | cons thread rest ih =>
    cases first : tick cfg ctx code choose thread s with
    | none => simp [execute,first] at executed
    | some next =>
      cases last : execute cfg ctx code choose rest next.state with
      | none => simp [execute,first,last] at executed
      | some final =>
        simp [execute,first,last] at executed
        subst out
        exact .cons (tick_sound first) (ih last)

end PtxTorchLean.Poisson.PTX.CellEntry

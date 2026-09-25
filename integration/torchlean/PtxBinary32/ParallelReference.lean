import PtxBinary32.Parallel

/-! A selected software execution witness. Ordinary loads read the arena and
FP instructions choose the checked binary32 reference. The candidate relation
still admits other read values and all results in its numerical envelope. -/
namespace Ptx.Scalar.Parallel.Reference

def binary32 (i : Scalar.Binary32.Instr) (s : Scalar.State) :
    Scalar.State × Scalar.Binary32.Occurrence :=
  if i.guard.eval s then
    ({{s with pc := s.pc+1} with regs := Scalar.update s.regs i.destination (Ptx.Binary32.reference i.operation (i.left.eval s) (i.right.eval s))},
      Scalar.Binary32.occurrence s i true)
  else ({s with pc := s.pc+1},Scalar.Binary32.occurrence s i false)

theorem binary32_sound (i : Scalar.Binary32.Instr) (s : Scalar.State) :
    Scalar.Binary32.Eval i s (binary32 i s).1 (binary32 i s).2 := by
  unfold binary32
  split
  · exact .executed (by assumption) (Ptx.Binary32.envelope_self _)
  · exact .skipped (Bool.eq_false_of_not_eq_true (by assumption))

def dispatch (cfg : Config n) (thread : Fin n) (i : Instr) (s : State n) : Outcome n :=
  match i with
  | .localStep i => scalarStep none thread none i s
  | .memory space i => scalarStep none thread (some space) i s
  | .binary32 i =>
    let result := binary32 i (s.lanes thread).scalar
    ⟨setLane s thread {s.lanes thread with scalar := result.1},.advanced,[.binary32 thread result.2]⟩
  | .sync r => synchronize cfg s thread r
  | .exit => ⟨setLane s thread {s.lanes thread with halted := true},.halted,
      [.exit thread (s.lanes thread).scalar.pc]⟩

theorem dispatch_sound (cfg : Config n) (thread : Fin n) (i : Instr) (s : State n) :
    Dispatch cfg none thread i s (dispatch cfg thread i s) := by
  cases i with
  | localStep i => exact .localStep
  | memory space i => exact .memory
  | binary32 i => exact .binary32 (binary32_sound i _)
  | sync r => exact .sync
  | exit => exact .exit

def step (cfg : Config n) (program : List Instr) (thread : Fin n) (s : State n) : Outcome n :=
  if (s.lanes thread).halted then ⟨s,.halted,[]⟩
  else if s.barrier.arrived thread then ⟨s,.waiting,[]⟩
  else match program[(s.lanes thread).scalar.pc]? with
    | none => ⟨s,.invalidPC,[]⟩
    | some i => dispatch cfg thread i s

theorem step_sound (cfg : Config n) (program : List Instr) (thread : Fin n) (s : State n)
    (eligible : Mixed.Eligible cfg.target) : Step cfg program none thread s (step cfg program thread s) := by
  refine ⟨eligible,?_⟩
  unfold step
  split
  · rfl
  · split
    · rfl
    · split
      · simp_all
      · simpa only [show program[(s.lanes thread).scalar.pc]? = some _ from by assumption] using dispatch_sound cfg thread _ s

/-- Statuses are retained: a finite schedule may fault or stop short of exit.
A concrete completion theorem must check its final state and these outcomes. -/
def run (cfg : Config n) (program : List Instr) (s : State n) :
    List (Fin n) → State n × List (Event n) × List Status
  | [] => (s,[],[])
  | t::ts =>
    let out := step cfg program t s
    let rest := run cfg program out.state ts
    (rest.1,out.events++rest.2.1,out.status::rest.2.2)

theorem run_sound (cfg : Config n) (program : List Instr) (s : State n) (schedule : List (Fin n))
    (eligible : Mixed.Eligible cfg.target) :
    Runs cfg program s (run cfg program s schedule).2.1 (run cfg program s schedule).1 := by
  induction schedule generalizing s with
  | nil => exact .nil
  | cons t ts ih => exact .cons (step_sound cfg program t s eligible) (ih _)

end Ptx.Scalar.Parallel.Reference

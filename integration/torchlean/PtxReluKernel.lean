import PtxBinary32.Sequential
import PtxBinary32.ReluGate
import PtxBinary32.BackwardError
import PtxReluVJP

/-! Serialized, separately authored ReLU-neuron kernels. Arguments designate
initialized words in one allocation; launches provide completion and visibility. -/
namespace PtxTorchLean.ReluKernel
open Ptx Ptx.Scalar Ptx.Scalar.Sequential Ptx.SequentialStorage

structure Data where
  x : Word
  w : Word
  b : Word
  a : Word
  y : Word
  seed : Word
  db : Word
  dx : Word
  dw : Word
  tail : List Word

def Data.words (d : Data) : List Word := [d.x,d.w,d.b,d.a,d.y,d.seed,d.db,0,d.dx,d.dw] ++ d.tail

inductive Stage where
  | affine | forward | backward | dx | dw
  deriving DecidableEq, Repr

def Stage.isGate : Stage → Bool
  | .forward | .backward => true
  | _ => false

def program (stage : Stage) : List Mixed.Instr :=
  if stage.isGate then ReluGate.program else Affine.program

def arguments (allocation : Nat) (stage : Stage) (i : Fin 4) : Argument :=
  ⟨allocation, match stage, i.val with
    | .affine, 0 => 4 | .affine, 1 => 0 | .affine, 2 => 8 | .affine, _ => 12
    | .forward, 0 => 12 | .forward, 1 => 12 | .forward, _ => 16
    | .backward, 0 => 12 | .backward, 1 => 20 | .backward, _ => 24
    | .dx, 0 => 24 | .dx, 1 => 4 | .dx, 2 => 28 | .dx, _ => 32
    | .dw, 0 => 24 | .dw, 1 => 0 | .dw, 2 => 28 | .dw, _ => 36⟩

def Data.update (d : Data) : Stage → Word → Data
  | .affine, v => {d with a := v}
  | .forward, v => {d with y := v}
  | .backward, v => {d with db := v}
  | .dx, v => {d with dx := v}
  | .dw, v => {d with dw := v}

def Results (d : Data) : Stage → Word → Prop
  | .affine, v => ∃ p, Binary32.Error.AffineResults d.w d.x d.b p v
  | .forward, v => v = Binary32.Relu.forward d.a
  | .backward, v => v = Binary32.Relu.gate d.a d.seed
  | .dx, v => ∃ p, Binary32.Error.AffineResults d.db d.w 0 p v
  | .dw, v => ∃ p, Binary32.Error.AffineResults d.db d.x 0 p v

def stageStart (d : Data) (allocation : Nat) (stage : Stage) (registers : Seed) : State :=
  start registers (arguments allocation stage) d.words

def request (target : Target) (thread : ThreadLocation) (allocation : Nat)
    (registers : Stage → Seed) (stage : Stage) : Request :=
  ⟨target, program stage, thread, allocation, 4, arguments allocation stage, registers stage⟩

def forwardStages : List Stage := [.affine, .forward]
def backwardStages : List Stage := [.affine, .backward, .dx, .dw]

/-- Arithmetic of the executed stages, derived below from actual fetched runs. -/
inductive Evaluation : Data → List Stage → Data → Prop
  | nil : Evaluation d [] d
  | cons : Results d stage v → Evaluation (d.update stage v) rest out → Evaluation d (stage::rest) out

private theorem affine_initial (d : Data) (allocation : Nat) (stage : Stage) (registers : Seed)
    (ordinary : stage.isGate = false) : Affine.Initial (stageStart d allocation stage registers) := by
  constructor
  · rfl
  · intro i
    cases stage <;> fin_cases i <;> simp_all [Stage.isGate, stageStart, start, arguments, Data.words, ValidAddress]

private theorem gate_initial (d : Data) (allocation : Nat) (stage : Stage) (registers : Seed)
    (gated : stage.isGate = true) : ReluGate.Initial (stageStart d allocation stage registers) := by
  constructor
  · rfl
  · intro i
    cases stage <;> fin_cases i <;> simp_all [Stage.isGate, stageStart, start, arguments, Data.words, ValidAddress]

private theorem affine_memory (d : Data) (allocation : Nat) (stage : Stage) (registers : Seed)
    (ordinary : stage.isGate = false) (p v : Word) :
    (Affine.finish (stageStart d allocation stage registers) p v).memory = (d.update stage v).words := by
  cases stage <;> simp_all [Stage.isGate, Affine.finish, Affine.afterAdd, Affine.afterMultiply,
    Affine.afterBias, Affine.afterRight, Affine.afterLeft, Affine.outputIndex,
    stageStart, start, arguments, Data.words, Data.update]

private theorem gate_memory (d : Data) (allocation : Nat) (stage : Stage) (registers : Seed)
    (gated : stage.isGate = true) :
    ∃ v, Results d stage v ∧ (ReluGate.finish (stageStart d allocation stage registers)).memory =
      (d.update stage v).words := by
  cases stage <;> simp_all [Stage.isGate, Results, ReluGate.finish, ReluGate.input,
    stageStart, start, arguments, Data.words, Data.update, Binary32.Relu.forward]

theorem run_correct (d : Data) (allocation : Nat) (stage : Stage) (registers : Seed)
    (eligible : Mixed.Eligible target)
    (run : Mixed.Run target (program stage) (stageStart d allocation stage registers) final .halted events) :
    ∃ v, Results d stage v ∧ final.memory = (d.update stage v).words := by
  cases hg : stage.isGate
  · obtain ⟨p,v,hv,hf,_,_⟩ := (Affine.run_iff _ target (affine_initial d allocation stage registers hg)
      eligible _ _ _).mp (by simpa [program, hg] using run)
    refine ⟨v, ?_, hf ▸ affine_memory d allocation stage registers hg p v⟩
    cases stage <;> simp_all [Stage.isGate, Results, Affine.input, stageStart, start, arguments, Data.words]
    all_goals exact ⟨p,hv⟩
  · have hf := ((ReluGate.run_iff _ target (gate_initial d allocation stage registers hg)
      eligible final .halted).mp ⟨events, by simpa [program, hg] using run⟩).1
    rw [hf]
    exact gate_memory d allocation stage registers hg

theorem run_exists (d : Data) (allocation : Nat) (stage : Stage) (registers : Seed)
    (eligible : Mixed.Eligible target) :
    ∃ final events, Mixed.Run target (program stage) (stageStart d allocation stage registers) final .halted events := by
  cases hg : stage.isGate
  · simpa [program, hg] using Affine.run_exists _ target (affine_initial d allocation stage registers hg) eligible
  · obtain ⟨events, run⟩ := ReluGate.run_exists _ target (gate_initial d allocation stage registers hg) eligible
    exact ⟨_, events, by simpa [program, hg] using run⟩

variable {target : Target} {thread : ThreadLocation} {allocation : Nat} {registers : Stage → Seed}
  {before after : Store} {d : Data}

theorem launch_correct (present : before.cells allocation = some ⟨thread.device,d.words⟩)
    (eligible : Mixed.Eligible target)
    (launch : SuccessfulLaunch (request target thread allocation registers stage) before after final events) :
    ∃ v, Results d stage v ∧ after.cells allocation = some ⟨thread.device,(d.update stage v).words⟩ := by
  obtain ⟨v,hv,hm⟩ := run_correct d allocation stage (registers stage) eligible (launch.run_from present)
  exact ⟨v,hv, by simpa only [request, hm] using launch.writeback_lookup present⟩

theorem launch_exists (present : before.cells allocation = some ⟨thread.device,d.words⟩)
    (eligible : Mixed.Eligible target) (stage : Stage) :
    ∃ after final events, SuccessfulLaunch (request target thread allocation registers stage) before after final events := by
  obtain ⟨final,events,run⟩ := run_exists d allocation stage (registers stage) eligible
  obtain ⟨after,launch⟩ := Sequential.launch_exists
    (request := request target thread allocation registers stage) present rfl (fun _ => rfl) run
  exact ⟨after,final,events,launch⟩

theorem pipeline_correct (stages : List Stage)
    (present : before.cells allocation = some ⟨thread.device,d.words⟩)
    (eligible : Mixed.Eligible target)
    (chain : Chain before (stages.map (request target thread allocation registers)) after) :
    ∃ out, Evaluation d stages out ∧ after.cells allocation = some ⟨thread.device,out.words⟩ := by
  induction stages generalizing before d with
  | nil => cases chain; exact ⟨d,.nil,present⟩
  | cons stage rest ih =>
    cases chain with
    | cons launch chain =>
      obtain ⟨v,hv,saved⟩ := launch_correct present eligible launch
      obtain ⟨out,ev,saved'⟩ := ih saved chain
      exact ⟨out,.cons hv ev,saved'⟩

theorem pipeline_exists (stages : List Stage)
    (present : before.cells allocation = some ⟨thread.device,d.words⟩)
    (eligible : Mixed.Eligible target) :
    ∃ after, Chain before (stages.map (request target thread allocation registers)) after := by
  induction stages generalizing before d with
  | nil => exact ⟨before,.nil⟩
  | cons stage rest ih =>
    obtain ⟨middle,final,events,launch⟩ := launch_exists (registers := registers) present eligible stage
    obtain ⟨v,_,saved⟩ := launch_correct present eligible launch
    obtain ⟨after,chain⟩ := ih saved
    exact ⟨after,.cons launch chain⟩

/-- Every executed load/store is aligned and within the supplied allocation. -/
theorem launch_memory_safe (present : before.cells allocation = some ⟨thread.device,d.words⟩)
    (launch : SuccessfulLaunch (request target thread allocation registers stage) before after final events)
    (member : event ∈ events) (access : event.memory = some effect) :
    ValidAddress d.words effect.address :=
  (launch.run_from present).memory_safe member access

/-- Executing these requests preserves every other allocation. -/
theorem pipeline_frame (stages : List Stage)
    (chain : Chain before (stages.map (request target thread allocation registers)) after)
    (other : Nat) (different : other ≠ allocation) : after.cells other = before.cells other := by
  induction stages generalizing before with
  | nil => cases chain; rfl
  | cons stage rest ih =>
    cases chain with
    | cons launch chain => exact (ih chain).trans (launch.other_cell different)

/-- The computation never overwrites its input, weight, bias, incoming seed or trailing storage. -/
theorem Evaluation.inputs_frame (ev : Evaluation d stages out) :
    out.x = d.x ∧ out.w = d.w ∧ out.b = d.b ∧ out.seed = d.seed ∧ out.tail = d.tail := by
  induction ev with
  | nil => simp
  | @cons d stage v rest out hv ev ih => cases stage <;> simpa [Data.update] using ih

end PtxTorchLean.ReluKernel

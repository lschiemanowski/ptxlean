import PoissonPTX.DotInputLayout
import PoissonPTX.ControlFlowSequence

namespace PtxTorchLean.Poisson.PTX.DotInput

/-- The shared symbol is represented by its launch-allocated address. The copy
of the lane register uses the zero-extended lane value just read from context. -/
def setupCode (scratch : Word) : List Flow.Instr :=
  [.data (.data (.mov 3 (.imm scratch))),.context 0 .arena,.context 14 .lane,.context 15 .group,
    .data (.data (.mov 12 (.reg 14))),.data (.data (.mov 8 (.imm 0)))]

def setup (ctx : Kernel.Context) (scratch : Word) (s : Flow.State) : Flow.State :=
  {s with core:=assign (assign (assign (assign (assign (assign s.core 3 scratch)
    0 ctx.arena) 14 (ctx.lane.setWidth 64)) 15 (ctx.group.setWidth 64))
    12 (ctx.lane.setWidth 64)) 8 0}

theorem setup_sequence (running : s.halted=false) :
    Flow.Sequence ctx (setupCode scratch) s (setup ctx scratch s) := by
  apply Flow.sequence_sound
  simp [Flow.sequence,Flow.eval,Flow.simple,Flow.source,Indexed.eval,PTX.eval,Operand.eval,
    setupCode,setup,assign,advance,running]

/-- The emitted mov.u32 copy and the model's bit copy agree here because the
preceding context read establishes a zero-extended 32-bit source. -/
theorem lane_copy (lane : BitVec 32) :
    (Kernel.u32 (lane.setWidth 64)).setWidth 64=lane.setWidth 64 := by
  simp [Kernel.u32]

theorem setup_cursor : cursor (setup ctx scratch s).core=ctx.lane.toNat := by
  simp [cursor,setup,assign,advance,Kernel.u32]

theorem setup_zero : decode ((setup ctx scratch s).core.regs 8)=0 := by
  change decode (0 : Word)=0
  rfl

def inputProgram (count : Nat) (left right scratch : Word) : List Flow.Instr :=
  Flow.OperandWindow.program (setupCode scratch) 12 (.imm (BitVec.ofNat 64 count))
    ((body left right).map Indexed.Instr.data) []

theorem input_length : (inputProgram count left right scratch).length=20 := by
  simp [inputProgram,Flow.OperandWindow.program,Flow.OperandWindow.header,setupCode,
    body,loadCode,addressCode]

/-- Read the setup from the actual fetched prefix, using its proved sequence
only to identify deterministic instruction effects. -/
theorem consume_setup
    (run : Flow.Counted ctx (inputProgram count left right scratch) steps s t)
    (pc : s.core.pc=0) (running : s.halted=false) (done : t.core.pc=20) :
    ∃ remaining, Flow.Counted ctx (inputProgram count left right scratch) remaining (setup ctx scratch s) t := by
  have consume : ∀ (code : List Flow.Instr) (pre post : List Flow.Instr) s mid k,
      Flow.Sequence ctx code s mid → (∀ i∈code, Flow.noFP i=true) →
      (∀ i∈code, Flow.linear i=true) →
      Flow.Counted ctx (pre++code++post) k s t → s.core.pc=pre.length →
      pre.length+code.length≤t.core.pc →
      ∃ rest, Flow.Counted ctx (pre++code++post) rest mid t := by
    intro code pre post s mid k trace plain forward actual counter past
    induction trace generalizing pre k with
    | nil => exact ⟨k,actual⟩
    | @cons i s next code mid live one rest ih =>
      obtain ⟨number,seen,_,step,tail⟩ := Flow.Boundary.peel actual
        (by simp only [List.length_cons] at past; omega) (i:=i) (by simp [counter])
      have same := Flow.eval_unique step one (plain i (by simp))
      subst seen
      have nextPC : next.core.pc=(pre++[i]).length := by
        rw [Flow.linear_pc one (forward i (by simp)),counter]; simp
      obtain ⟨remaining,later⟩ := ih (pre++[i]) number (fun j h => plain j (by simp [h]))
        (fun j h => forward j (by simp [h]))
        (by simpa [List.append_assoc] using tail) nextPC
        (by simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using past)
      exact ⟨remaining,by simpa [List.append_assoc] using later⟩
  apply consume (setupCode scratch) [] _ s (setup ctx scratch s) steps (setup_sequence running)
    (by simp [setupCode,Flow.noFP,Indexed.noFP,PTX.noFP]) (by simp [setupCode,Flow.linear])
    (by simpa [inputProgram,Flow.OperandWindow.program,Flow.OperandWindow.header,List.append_assoc] using run) pc
    (by simp [setupCode,done])

end PtxTorchLean.Poisson.PTX.DotInput

import PoissonPTX.DotStores
import PoissonPTX.ObservedWalk

namespace PtxTorchLean.Poisson.PTX.Concurrent.Dot

/-- The real loop predicate establishes a valid element index before either
load. Address facts follow the three actual address-preparation instructions. -/
def InputReady (count : Nat) (left right : Word) (s : Flow.State) : Prop :=
  (s.core.pc=7 → s.predicates 0=decide (count≤DotInput.cursor s.core)) ∧
  (8≤s.core.pc → s.core.pc≤18 → DotInput.cursor s.core<count) ∧
  (s.core.pc=9 ∨ s.core.pc=13 → s.core.regs 1=wide s.core 12) ∧
  (s.core.pc=10 ∨ s.core.pc=14 → s.core.regs 2=s.core.regs 0+wide s.core 12) ∧
  (s.core.pc=11 → s.core.regs 2=address s.core 12 left) ∧
  (s.core.pc=15 → s.core.regs 2=address s.core 12 right)

theorem input_ready_initial (entry : s.core.pc=0) : InputReady count left right s := by
  simp [InputReady,entry]

theorem count_word (bounded : count<2^30) :
    (Kernel.u32 (BitVec.ofNat 64 count)).toNat=count := by
  have small : count<2^32 := by omega
  simp [Kernel.u32,BitVec.toNat_ofNat]
  omega

theorem input_footprint_step
    (fetch : (DotInput.inputProgram count left right scratch)[s.core.pc]?=some i)
    (actual : Flow.Observed.Eval ctx i s t access index) (bounded : count<2^30)
    (ready : InputReady count left right s) : InputReady count left right t := by
  have bound : s.core.pc<20 := by
    have h := (List.getElem?_eq_some_iff.mp fetch).1
    simpa only [DotInput.input_length] using h
  generalize counter : s.core.pc=pc at fetch bound
  interval_cases pc <;>
    simp [DotInput.inputProgram,Flow.OperandWindow.program,Flow.OperandWindow.header,
      DotInput.setupCode,DotInput.body,loadCode,addressCode] at fetch <;> cases fetch
  all_goals cases actual
  all_goals try { rename_i ordinary; exact False.elim (ordinary _ rfl) }
  all_goals (first | cases_type* Indexed.Candidate.Data Concurrent.Data PTX.Eval | skip)
  all_goals simp_all [Concurrent.ordinary,InputReady,assign,advance,Operand.eval,
    Flow.simple,Flow.next,Flow.goto,Flow.source,Flow.Compare.apply,count_word bounded,
    DotInput.cursor,address,wide]
  all_goals split <;> simp_all
  all_goals
    have no : ¬count≤(Kernel.u32 (s.core.regs 12)).toNat := decide_eq_false_iff_not.mp (by assumption)
    omega

end PtxTorchLean.Poisson.PTX.Concurrent.Dot

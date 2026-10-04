import PoissonPTX.NativeFlowFrame
import PoissonPTX.NativeFlowRegion

namespace PtxTorchLean.Poisson.PTX.Concurrent.NativeFlow

variable {program : List Instr} {s t : Flow.State} {initPC r : Nat} {value : Word}

/-- A setup instruction establishes a register; every later use preserves it.
The control obligations rule out jumping across the setup from an earlier PC. -/
theorem initialized_flow
    (actual : Flow.Observed.Eval ctx i s t access index)
    (fetch : program[s.core.pc]?=some (.flow i))
    (ready : initPC<s.core.pc → s.core.regs r=value)
    (before : ∀ pc i, pc < initPC → program[pc]?=some (.flow i) → targets (· ≤ initPC) i)
    (assigns : ∀ i s t access index, s.core.pc=initPC → program[initPC]?=some (.flow i) →
      Flow.Observed.Eval ctx i s t access index → t.core.regs r=value)
    (preserves : ∀ pc i, initPC<pc → program[pc]?=some (.flow i) → keeps r i) :
    initPC<t.core.pc → t.core.regs r=value := by
  intro later
  rcases lt_trichotomy s.core.pc initPC with early | same | past
  · have bound := eval_upper actual early (before _ _ early fetch); omega
  · exact assigns i s t access index same (same ▸ fetch) actual
  · exact (eval_keeps actual (preserves _ _ past fetch)).trans (ready past)

theorem initialized_sync
    (ready : initPC<s.core.pc → s.core.regs r=value)
    (fetch : program[s.core.pc]?=some (.sync resource))
    (ordinary : program[initPC]?≠some (.sync resource)) :
    initPC<(Flow.next s).core.pc → (Flow.next s).core.regs r=value := by
  intro later
  have different : s.core.pc≠initPC := by intro same; exact ordinary (same ▸ fetch)
  apply ready
  change initPC<s.core.pc+1 at later
  omega

end PtxTorchLean.Poisson.PTX.Concurrent.NativeFlow

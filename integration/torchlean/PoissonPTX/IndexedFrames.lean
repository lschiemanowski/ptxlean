import PoissonPTX.IndexedBlocks
import PoissonPTX.SharedStore

namespace PtxTorchLean.Poisson.PTX.Indexed

def keeps (r : Nat) : Instr → Prop
  | .data op => SharedStore.keeps r op
  | .mad32 dst .. | .wide4 dst .. | .load32 dst .. => r≠dst

theorem eval_keeps (run : Eval op s t) (frame : keeps r op) : t.regs r=s.regs r := by
  cases run with
  | data one => exact SharedStore.eval_keeps one frame
  | _ => simp_all [keeps,assign,advance]

theorem block_keeps (run : Block code s t) (frame : ∀ op∈code, keeps r op) : t.regs r=s.regs r := by
  induction run with
  | nil => rfl
  | cons one rest ih =>
    exact (ih (fun op member => frame op (by simp [member]))).trans
      (eval_keeps one (frame _ (by simp)))

theorem scalar_block (run : PTX.Block code s t) : Block (code.map Instr.data) s t := by
  induction run with
  | nil => exact .nil
  | cons one rest ih => exact .cons (.data one) ih

end PtxTorchLean.Poisson.PTX.Indexed

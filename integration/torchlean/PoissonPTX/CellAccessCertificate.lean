import PoissonPTX.CellAccessBounds

namespace PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.Witness
open CellMiddle Symbolic

/-- Check one instruction in its already-computed symbolic address state. -/
def AccessSafe (width : Nat) (regs : Symbolic.Registers) : Instr → Prop
  | .data (.load64 space _ address) | .data (.store64 space address _) =>
    match Numeric.extract (operand regs address) with
    | some (sp,off) => sp=space ∧ off.toNat%8=0 ∧ off.toNat+8≤extent width space
    | none => False
  | _ => True

instance : Decidable (AccessSafe width regs i) := by
  unfold AccessSafe
  split
  · split <;> infer_instance
  · split <;> infer_instance
  · infer_instance

/-- Linear traversal avoids reinterpreting every earlier prefix at each PC. -/
def SequenceSafe (width : Nat) (regs : Symbolic.Registers) : List Instr → Prop
  | [] => True
  | i::rest => AccessSafe width regs i ∧ SequenceSafe width (transfer .addresses regs i) rest

instance (width : Nat) (regs : Symbolic.Registers) (code : List Instr) : Decidable (SequenceSafe width regs code) := by
  induction code generalizing regs with
  | nil => exact inferInstanceAs (Decidable True)
  | cons i rest ih => exact instDecidableAnd

theorem sequence_safe_at {code : List Instr} (safe : SequenceSafe width regs code) (fetch : code[pc]?=some i) :
    AccessSafe width (atPC .addresses code regs pc) i := by
  induction code generalizing regs pc with
  | nil => simp at fetch
  | cons first rest ih =>
    cases pc with
    | zero =>
      simp only [List.getElem?_cons_zero,Option.some.injEq] at fetch
      subst i
      exact safe.1
    | succ pc =>
      have atRest := ih safe.2 (by simpa using fetch)
      simpa only [atPC,List.take_succ_cons,List.foldl_cons] using atRest

def Certificate (width : Nat) : Prop :=
  ∀ lane : Fin (width*width), SequenceSafe width (Numeric.seed width lane.val) (program width)

instance : Decidable (Certificate width) := by unfold Certificate; infer_instance

theorem certificate_bounds (certificate : Certificate width) : AccessBounds width := by
  intro lane pc
  have found := List.getElem?_eq_getElem pc.isLt
  have safe := sequence_safe_at (certificate lane) found
  unfold accessCheck
  rw [found]
  cases item : (program width)[pc.val] with
  | data op => rw [item] at safe; cases op <;> exact safe
  | skip => trivial
  | sync => trivial

end PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.Witness

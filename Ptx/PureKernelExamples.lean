import Ptx.ReviewedPure

namespace Ptx.Scalar.PureKernelExamples
open PureKernel

def choiceFamily : Pure32.Family Unit where
  wordArity := fun _ => 0
  predicateArity := fun _ => 0
  Results := fun _ _ _ value => value = 0 ∨ value = 1
  inhabited := fun _ _ _ => ⟨0,Or.inl rfl⟩
  Supported := fun target _ => 90 ≤ target.sm

def choiceCatalog : Catalog Unit := ⟨fun _ => Unit, fun _ => choiceFamily⟩
def choice : Pure32.Instr choiceFamily := ⟨.always, (), 0, Fin.elim0, Fin.elim0⟩
def start (s : State) : State := {s with pc := 0}

theorem two_outcomes (s : State) :
    Dispatch ⟨94,90⟩ [Instr.pure (catalog := choiceCatalog) () choice] (start s)
      (.next (Pure32.write (start s) 0 0) (.pure () (Pure32.occurrence (start s) choice true))) ∧
    Dispatch ⟨94,90⟩ [Instr.pure (catalog := choiceCatalog) () choice] (start s)
      (.next (Pure32.write (start s) 0 1) (.pure () (Pure32.occurrence (start s) choice true))) ∧
    Pure32.write (start s) 0 0 ≠ Pure32.write (start s) 0 1 := by
  exact dispatch_preserves_choices (catalog := choiceCatalog) (target := ⟨94,90⟩)
    (s := start s) (kind := ()) (i := choice) (a := 0) (b := 1)
    (by constructor <;> decide) rfl (by change 90 ≤ 90; decide)
    rfl (Or.inl rfl) (Or.inr rfl) (by decide)

/-- A false guard cannot hide an unsupported family feature requirement. -/
theorem skipped_target_rejected (s : State) (disabled : s.preds 0 = false) :
    let i : Pure32.Instr choiceFamily := {choice with guard := .pred 0 true}
    i.guard.eval (start s) = false ∧
    Dispatch ⟨94,80⟩ [Instr.pure (catalog := choiceCatalog) () i] (start s)
      (.unsupported "pure family target") := by
  constructor
  · simp [Guard.eval, start, disabled]
  · exact (dispatch_unsupported rfl (by change ¬ (90 ≤ 80); decide) (by constructor <;> decide)).mpr rfl

theorem outside_domain (s : State) :
    Dispatch ⟨93,90⟩ ([] : List ReviewedPure.Instr) s (.unsupported "kernel target") := by
  apply (dispatch_ineligible ?_).mpr rfl
  intro h
  have : (93 : Nat) = 94 := h.1
  contradiction

def branchProgram : List ReviewedPure.Instr :=
  [.scalar (.plain (.bra 2)), .scalar (.plain (.unsupported "unreachable")), .scalar (.plain .exit)]

theorem branch_exit (s : State) (eligible : Eligible target) :
    ∃ trace, Run target branchProgram (start s) {s with pc := 2} .halted trace := by
  refine ⟨[.scalar (Scalar.occurrence (start s) (.plain (.bra 2)) true),
    .scalar (Scalar.occurrence {s with pc := 2} (.plain .exit) true)],
    Run.next (next := {s with pc := 2}) ?_ (Run.halted ?_)⟩
  · apply (dispatch_fetch eligible (by rfl) (by trivial)).mpr
    exact eval_scalar_iff.mpr rfl
  · apply (dispatch_fetch eligible (by rfl) (by trivial)).mpr
    exact eval_scalar_iff.mpr rfl

theorem missing_pc (s : State) (eligible : Eligible target) :
    Run target ([] : List ReviewedPure.Instr) s s (.fault (.invalidPC s.pc)) [] := by
  apply Run.fault
  classical
  simp [Dispatch, eligible]

theorem misaligned_load (s : State) (eligible : Eligible target) :
    Run target ([.scalar (.plain (.load 0 (.imm 2)))] : List ReviewedPure.Instr)
      (start s) (start s) (.fault (.misaligned 2)) [] := by
  apply Run.fault
  apply (dispatch_fetch eligible (by rfl) (by trivial)).mpr
  apply eval_scalar_iff.mpr
  rfl

end Ptx.Scalar.PureKernelExamples

import PoissonPTX.ScalarMemory

namespace PtxTorchLean.Poisson.PTX.Scalar

theorem sqrt_result (actual : Sequence ctx [.sqrt dst a] s t) :
    ∃ value, t={s with core:=assign s.core dst value} ∧ decode value=Float.sqrt (decode (a.eval s.core)) := by
  cases actual with
  | cons running step rest =>
    cases rest
    cases step with
    | sqrt allowed => exact ⟨_,rfl,allowed⟩
    | simple ordinary => simp [Scalar.ordinary] at ordinary

theorem max_result (actual : Sequence ctx [.max dst a b] s t) :
    ∃ value, t={s with core:=assign s.core dst value} ∧ decode value=maximum (a.eval s.core) (b.eval s.core) := by
  cases actual with
  | cons running step rest =>
    cases rest
    cases step with
    | max allowed => exact ⟨_,rfl,allowed⟩
    | simple ordinary => simp [Scalar.ordinary] at ordinary

theorem fp_result (actual : Sequence ctx [.base (.data (.data (.fp op dst a b)))] s t) :
    ∃ value, t={s with core:=assign s.core dst value} ∧ FP.Result op (a.eval s.core) (b.eval s.core) value := by
  obtain ⟨block,state⟩ := ops_block (code:=[.fp op dst a b]) actual
  generalize finalCore : t.core=last at block
  cases block with
  | cons step rest =>
    cases rest
    cases step with
    | fp allowed =>
      refine ⟨_,?_,allowed⟩
      rw [state,finalCore]

end PtxTorchLean.Poisson.PTX.Scalar

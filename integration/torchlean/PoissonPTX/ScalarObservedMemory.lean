import PoissonPTX.ScalarObserved
import PoissonPTX.ScalarPublication

namespace PtxTorchLean.Poisson.PTX.Scalar.Observed

theorem extra_memory (actual : Scalar.Eval ctx i s t) (plain : extra i=true) : t.core.memory=s.core.memory := by
  cases actual with
  | base => simp [extra] at plain
  | store32 => simp [extra] at plain
  | simple ordinary =>
    cases i <;> simp_all [Scalar.ordinary,extra]
    all_goals first | rfl | (simp only [Scalar.simple]; split <;> rfl)
  | _ => rfl

theorem base_data_memory (actual : Indexed.Candidate.Data op s t word index) :
    t.memory=Sources.publish s.memory (records word index) := by
  cases actual with
  | data actual =>
    cases actual with
    | ordinary plain actual =>
      cases actual <;> simp_all [Concurrent.ordinary]
      all_goals rfl
    | load => rfl
    | @store sp addr src s valid =>
      funext space
      cases sp <;> cases space <;> rfl
  | mad32 => rfl
  | wide4 => rfl
  | load32 => rfl

theorem eval_memory (actual : Eval ctx i s t events) :
    t.core.memory=Sources.publish s.core.memory events := by
  cases actual with
  | extra plain actual => exact extra_memory actual plain
  | store32 valid =>
    funext space
    cases space with
    | global =>
      simp [Sources.publish,Sources.applyAccess,Sources.flag,put32,PTX.State.memory,Kernel.u32,
        BitVec.setWidth_setWidth_of_le _ (by decide : 32≤64)]
    | shared => rfl
  | base actual =>
    cases actual with
    | data actual => exact base_data_memory actual
    | simple ordinary =>
      rename_i op
      cases op <;> simp only [Flow.simple]
      all_goals first | rfl | (split <;> rfl)

theorem runs_memory (actual : Runs ctx program s events t) :
    t.core.memory=Sources.publish s.core.memory events := by
  induction actual with
  | nil => rfl
  | cons step rest ih =>
    obtain ⟨_,_,_,effect⟩ := step
    rw [Sources.publish_append,← eval_memory effect]
    exact ih

end PtxTorchLean.Poisson.PTX.Scalar.Observed

import PoissonPTX.ScalarSources

namespace PtxTorchLean.Poisson.PTX.Scalar.SourceChecks

def futureFlag : List Sources.Access := [Sources.flag 0 false 0 1,Sources.flag 1 true 0 1]
def laterSource (_ : Nat) (k : Fin 8) : PTX.Sources.Origin Nat := .store 1 k

/-- Matching bytes alone would allow a read to invent its value from a later
same-thread write, even though the initial memory contains zero. -/
theorem future_flag_compatible : Sources.Compatible (fun _ _ => 0) futureFlag laterSource := by
  intro r ra found read k small
  cases r with
  | zero =>
    have same : ra=Sources.flag 0 false 0 1 := by simpa [futureFlag] using found.symm
    subst ra
    exact ⟨Sources.flag 1 true 0 1,rfl,rfl,rfl,small,rfl,rfl⟩
  | succ r =>
    cases r with
    | zero =>
      have same : ra=Sources.flag 1 true 0 1 := by simpa [futureFlag] using found.symm
      subst ra
      simp [Sources.flag] at read
    | succ r => simp [futureFlag] at found

theorem future_flag_not_admitted : ¬Sources.NoFuture futureFlag laterSource := by
  intro admitted
  have bad := admitted 0 1 (Sources.flag 0 false 0 1) (Sources.flag 1 true 0 1)
    rfl rfl rfl rfl rfl rfl rfl (by decide) ⟨0,by decide⟩ ⟨0,by decide⟩
  exact bad rfl

/-- A four-byte store cannot supply a fifth byte, even though the common
source-index type has room for all eight numerical-word bytes. -/
theorem fifth_flag_byte_rejected :
    ¬Sources.Compatible (fun _ _ => 0) futureFlag (fun _ _ => .store 1 ⟨4,by decide⟩) := by
  intro compatible
  have bad := compatible 0 (Sources.flag 0 false 0 1) rfl rfl ⟨0,by decide⟩ (by decide)
  obtain ⟨wa,found,write,space,small,address,value⟩ := bad
  have same : wa=Sources.flag 1 true 0 1 := by simpa [futureFlag] using found.symm
  subst wa
  simp [Sources.flag,Sources.Width.bytes] at small

end PtxTorchLean.Poisson.PTX.Scalar.SourceChecks

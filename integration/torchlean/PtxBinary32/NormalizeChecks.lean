import PtxBinary32.NormalizeProgram

/-! Fetch, target and register-lifetime checks for normalization. -/
namespace Ptx.Scalar.Normalize.Checks

/-- Explicit nearest-even arithmetic; neither operation uses FTZ. -/
theorem spellings : (text 0 1 2).map (·.mnemonic) =
    ["rcp.rn.f32", "mul.rn.f32"] := by decide

theorem missing_fetch (target : Ptx.Target) (s t : Scalar.State) :
    ¬ Run target [] s t := by
  rintro ⟨_,_,_,⟨_,i,fetch,_⟩,_⟩
  simp at fetch

theorem unsupported_target (target : Ptx.Target) (p : List Instr) (s t : Scalar.State)
    (unsupported : ¬ Scalar.Binary32.SupportedTarget target) : ¬ Run target p s t := by
  rintro ⟨_,_,_,⟨supported,_⟩,_⟩
  exact unsupported supported

/-- Destructive reuse of the denominator is supported for arbitrary words. -/
theorem denominator_alias (s : Scalar.State) (start : s.pc = 0) :
    ∃ t, Run ⟨94,20⟩ (program 0 1 1) s t ∧
      t.pc = 2 ∧ t.regs 0 = s.regs 0 ∧ t.memory = s.memory := by
  obtain ⟨t,run⟩ := execution_exists ⟨94,20⟩ s 0 1 1
    (by norm_num [Scalar.Binary32.SupportedTarget]) start (by decide)
  have f := (run_results ⟨94,20⟩ s t 0 1 1 start (by decide) run).2
  exact ⟨t,run,f.1,f.2.2.2.2 0 (by decide),f.2.1⟩

private def initial : Scalar.State :=
  ⟨0,(fun r => if r=0 then 0x40000000 else 0x40800000),
    (fun _ => 7),(fun _ => true),[0x12345678]⟩

/-- The scratch restriction is necessary: overwriting the numerator turns
2/4 into (1/4)*(1/4)=1/16, rather than the intended result 1/2. -/
theorem numerator_alias_changes_computation : ∃ t,
    Run ⟨94,20⟩ (program 0 1 0) initial t ∧
    t.regs 0 = 0x3d800000 ∧ t.regs 0 ≠ 0x3f000000 := by
  let middle : Scalar.State := {initial with pc:=1, regs:=Scalar.update initial.regs 0 0x3e800000}
  let t : Scalar.State := {middle with pc:=2, regs:=Scalar.update middle.regs 0 0x3d800000}
  have r₀ : Ptx.Binary32.Reciprocal.Results 0x40800000 0x3e800000 := by decide
  have r₁ : Ptx.Binary32.Results .mul 0x3e800000 0x3e800000 0x3d800000 := by unfold Ptx.Binary32.Results; decide
  have b₀ : Scalar.Reciprocal.Eval (reciprocal 1 0) initial middle
      (Scalar.Reciprocal.occurrence initial (reciprocal 1 0) true) := .executed rfl r₀
  have b₁ : Scalar.Binary32.Eval (multiply 0 0) middle t
      (Scalar.Binary32.occurrence middle (multiply 0 0) true) := .executed rfl r₁
  refine ⟨t,⟨middle,_,_,⟨?_,_,?_,.reciprocal b₀⟩,⟨?_,_,?_,.binary b₁⟩⟩,rfl,?_⟩
  · norm_num [Scalar.Binary32.SupportedTarget]
  · rfl
  · norm_num [Scalar.Binary32.SupportedTarget]
  · rfl
  · decide

end Ptx.Scalar.Normalize.Checks

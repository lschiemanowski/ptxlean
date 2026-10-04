import PoissonPTX.UpdateXRZLayout

namespace PtxTorchLean.Poisson.PTX.UpdateXRZ

/-- Recover the actual intermediate words and complete post-state in emitted
order. Geometry is an initial input condition; no intermediate memory contents
or arithmetic answers are supplied. -/
theorem state_result (actual : Flow.Sequence ctx (body alpha p x ap r diagonal boundary z) s final)
    (running : s.halted=false) (valid : Valid s.core alpha p x ap r diagonal boundary z) :
    ∃ xm xv rm rv zv,
      final=finish ctx s alpha p x ap r diagonal boundary z xm xv rm rv zv ∧
      decode xm=RegisterUpdate.product (coefficient s alpha).core p ∧
      decode xv=RegisterUpdate.result .add (coefficient s alpha).core p x ∧
      decode rm=RegisterUpdate.product (solution s alpha p x xm xv).core ap ∧
      decode rv=RegisterUpdate.result .sub (solution s alpha p x xm xv).core ap r ∧
      decode zv=PreconditionUpdate.result (residual s alpha p x ap r xm xv rm rv).core diagonal boundary := by
  obtain ⟨loaded,load,rest⟩ := Flow.sequence_split ((ScalarLoad.code 4 alpha).map (Flow.Instr.data ∘ Indexed.Instr.data))
    ((RegisterUpdate.code .add p x x).map (Flow.Instr.data ∘ Indexed.Instr.data) ++
      (RegisterUpdate.code .sub ap r r).map (Flow.Instr.data ∘ Indexed.Instr.data) ++ PreconditionUpdate.code diagonal boundary z)
    (by simpa only [body,List.append_assoc] using actual)
  obtain ⟨loadBlock,loadedState⟩ := Flow.scalar_segment load
  have eqLoaded : loaded=coefficient s alpha := by rw [loadedState,ScalarLoad.block_eq loadBlock]; rfl
  subst loaded
  have vc : Valid (coefficient s alpha).core alpha p x ap r diagonal boundary z := coefficient_geometry.valid valid
  obtain ⟨afterX,first,rest⟩ := Flow.sequence_split ((RegisterUpdate.code .add p x x).map (Flow.Instr.data ∘ Indexed.Instr.data))
    ((RegisterUpdate.code .sub ap r r).map (Flow.Instr.data ∘ Indexed.Instr.data) ++ PreconditionUpdate.code diagonal boundary z)
    (by simpa only [List.append_assoc] using rest)
  obtain ⟨firstBlock,firstState⟩ := Flow.scalar_segment first
  obtain ⟨xm,xv,xState,xProduct,xValue⟩ := RegisterUpdate.state_result firstBlock
    (vc.2.1 p (by simp)) (vc.2.1 x (by simp)) (vc.2.1 x (by simp))
  have eqX : afterX=solution s alpha p x xm xv := by rw [firstState,xState]; rfl
  subst afterX
  have vx : Valid (solution s alpha p x xm xv).core alpha p x ap r diagonal boundary z := solution_geometry.valid valid
  obtain ⟨afterR,second,last⟩ := Flow.sequence_split ((RegisterUpdate.code .sub ap r r).map (Flow.Instr.data ∘ Indexed.Instr.data))
    (PreconditionUpdate.code diagonal boundary z) rest
  obtain ⟨secondBlock,secondState⟩ := Flow.scalar_segment second
  obtain ⟨rm,rv,rState,rProduct,rValue⟩ := RegisterUpdate.state_result secondBlock
    (vx.2.1 ap (by simp)) (vx.2.1 r (by simp)) (vx.2.1 r (by simp))
  have eqR : afterR=residual s alpha p x ap r xm xv rm rv := by rw [secondState,rState]; rfl
  subst afterR
  have vr : Valid (residual s alpha p x ap r xm xv rm rv).core alpha p x ap r diagonal boundary z := residual_geometry.valid valid
  obtain ⟨zv,zState,zValue⟩ := PreconditionUpdate.state_result last running
    (vr.2.1 diagonal (by simp)) vr.2.2 (vr.2.1 z (by simp))
  exact ⟨xm,xv,rm,rv,zv,zState,xProduct,xValue,rProduct,rValue,zValue⟩

end PtxTorchLean.Poisson.PTX.UpdateXRZ

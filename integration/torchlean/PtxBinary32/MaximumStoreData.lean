import PtxBinary32.MaximumData
import PtxBinary32.MaximumControl

namespace Ptx.Scalar.Parallel.Maximum

private theorem emitted_store_value (a next : Scalar.State) (guard : Scalar.Guard) (address : Scalar.Operand64) (source : Nat)
    (occ : Scalar.Occurrence) (effect : MemoryEffect)
    (evaluated : Scalar.eval candidate ⟨guard,.store address (.reg source)⟩ a=.next next occ)
    (memory : occ.memory=some effect) : effect.value=a.regs source ∧ guard.eval a=true := by
  cases gate : guard.eval a <;> simp only [Scalar.eval,gate,↓reduceIte] at evaluated
  · obtain ⟨_,rfl⟩ := Scalar.StepResult.next.inj evaluated
    simp [Scalar.occurrence] at memory
  · split at evaluated
    · contradiction
    · obtain ⟨_,rfl⟩ := Scalar.StepResult.next.inj evaluated
      simp only [Scalar.occurrence,Option.some.injEq] at memory
      subst effect
      exact ⟨rfl,rfl⟩

/-- An emitted store writes the value justified by the live register invariant.
The fetched instruction and its actually executed guard determine the stage. -/
theorem scalar_store_data (d : Nat) (global : List Word) (t : Fin (width d))
    (a next : Scalar.State) (i : Scalar.Instr) (space : Space) (occ : Scalar.Occurrence) (effect : MemoryEffect)
    (data : Data d global t a) (fetch : (program d)[a.pc]?=some (.memory space i))
    (evaluated : Scalar.eval candidate i a=.next next occ) (memory : occ.memory=some effect) (store : effect.kind=.store) :
    StoreData d global t occ.pc effect.value := by
  have origin := Memory.Prior.eval_effect_origin candidate i a next occ effect evaluated memory
  have kind : Memory.Prior.memoryKind i.op=some .store := by simpa [store] using origin.2.2.2
  rw [origin.2.1]
  rcases fetched_store_site d a.pc space i fetch kind with ⟨site,rfl⟩ | ⟨k,hk,site,rfl⟩ | ⟨site,rfl⟩
  · have instruction : i=Scalar.Instr.plain (.store (.reg 0) (.reg 4)) := by
      simpa [site,program,publish,publishCode,Dense.pointer,Dense.scalar,Dense.guarded] using fetch.symm
    subst i
    have val := emitted_store_value a next _ _ _ occ effect evaluated memory
    rw [val.1]
    refine ⟨fun _ => data.publication (by omega) (by omega),?_,?_⟩
    · intro k hk h; omega
    · intro h; omega
  · rw [site,round_fetch d k hk 22 (by simp)] at fetch
    have instruction : i=⟨.pred 0 true,.store (.reg 3) (.reg 6)⟩ := by simpa [round,roundCode,roundSuffix,roundPrefix,Scalar.MaximumSelect.code,Dense.pointer,Dense.scalar,Dense.guarded] using fetch.symm
    subst i
    obtain ⟨value,gate⟩ := emitted_store_value a next _ _ _ occ effect evaluated memory
    have active : t.val<2^(d-(k+1)) := by
      simpa [Scalar.Guard.eval,data.roundGate k hk (by omega) (by omega)] using gate
    rw [value]
    refine ⟨?_,?_,?_⟩
    · intro h; omega
    · intro j hj h
      have eq : j=k := by omega
      subst j
      exact data.reduced k hk (by omega) (by omega) active
    · intro h; omega
  · rw [site,output_fetch d 10 (by simp)] at fetch
    have instruction : i=⟨.pred 0 true,.store (.reg 1) (.reg 6)⟩ := by simpa [output,outputCode,Dense.pointer,Dense.scalar,Dense.guarded] using fetch.symm
    subst i
    obtain ⟨value,gate⟩ := emitted_store_value a next _ _ _ occ effect evaluated memory
    have leader : t.val=0 := by simpa [Scalar.Guard.eval,data.outputGate (by omega) (by omega)] using gate
    rw [value]
    refine ⟨?_,?_,fun _ => data.root (by omega) (by omega) leader⟩
    · intro h; omega
    · intro j hj h; omega

end Ptx.Scalar.Parallel.Maximum

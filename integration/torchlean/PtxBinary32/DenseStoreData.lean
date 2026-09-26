import PtxBinary32.DenseData

namespace Ptx.Scalar.Parallel.Dense

private theorem emitted_store_value (a next : Scalar.State) (guard : Scalar.Guard) (address : Scalar.Operand64)
    (occ : Scalar.Occurrence) (effect : MemoryEffect)
    (evaluated : Scalar.eval candidate ⟨guard,.store address (.reg 6)⟩ a=.next next occ)
    (memory : occ.memory=some effect) : effect.value=a.regs 6 ∧ guard.eval a=true := by
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
theorem scalar_store_data (s : Shape) (global : List Word) (t : Fin s.threads)
    (a next : Scalar.State) (i : Scalar.Instr) (space : Space) (occ : Scalar.Occurrence) (effect : MemoryEffect)
    (data : Data s global t a) (fetch : (program s)[a.pc]?=some (.memory space i))
    (evaluated : Scalar.eval candidate i a=.next next occ) (memory : occ.memory=some effect) (store : effect.kind=.store) :
    StoreData s global t occ.pc effect.value := by
  have origin := Memory.Prior.eval_effect_origin candidate i a next occ effect evaluated memory
  have kind : Memory.Prior.memoryKind i.op=some .store := by simpa [store] using origin.2.2.2
  rw [origin.2.1]
  rcases fetched_store_site s a.pc space i fetch kind with ⟨site,rfl⟩ | ⟨k,hk,site,rfl⟩ | ⟨site,rfl⟩
  · have instruction : i=Scalar.Instr.plain (.store (.reg 2) (.reg 6)) := by
      simpa [site,program,products,pointer,scalar,guarded] using fetch.symm
    subst i
    have val := emitted_store_value a next _ _ occ effect evaluated memory
    rw [val.1]
    refine ⟨fun _ => data.product (by omega) (by omega),?_,?_⟩
    · intro k hk h; omega
    · intro h; omega
  · rw [site,round_fetch s k hk 14 (by simp)] at fetch
    have instruction : i=⟨.pred 0 true,.store (.reg 2) (.reg 6)⟩ := by simpa [round,pointer,scalar,guarded] using fetch.symm
    subst i
    obtain ⟨value,gate⟩ := emitted_store_value a next _ _ occ effect evaluated memory
    have active : t.val%s.width<2^(s.depth-(k+1)) := by
      simpa [Scalar.Guard.eval,data.roundGate k hk (by omega) (by omega)] using gate
    rw [value]
    refine ⟨?_,?_,?_⟩
    · intro h; omega
    · intro j hj h
      have eq : j=k := by omega
      subst j
      exact data.reduced k hk (by omega) (by omega) active
    · intro h; omega
  · rw [site,output_fetch s 18 (by simp)] at fetch
    have instruction : i=⟨.pred 0 true,.store (.reg 6) (.reg 6)⟩ := by simpa [output,pointer,scalar,guarded] using fetch.symm
    subst i
    obtain ⟨value,gate⟩ := emitted_store_value a next _ _ occ effect evaluated memory
    have leader : t.val%s.width=0 := by simpa [Scalar.Guard.eval,data.outputGate (by omega) (by omega)] using gate
    rw [value]
    refine ⟨?_,?_,fun _ => data.output (by omega) (by omega) leader⟩
    · intro h; omega
    · intro j hj h; omega

end Ptx.Scalar.Parallel.Dense

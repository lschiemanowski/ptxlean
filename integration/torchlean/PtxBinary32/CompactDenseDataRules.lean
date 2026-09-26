import PtxBinary32.CompactDenseDataStep
import PtxBinary32.DenseDataFP

/-! Compact per-group dense scratch. Arithmetic contracts are shared with Dense;
only the fetched shared addresses and their allocation change. -/
namespace Ptx.Scalar.Parallel.Dense.Compact
open Ptx.Binary32

/-- Classify any fetched instruction into one of the three program segments. -/
theorem program_segment (s : Shape) (pc : Nat) (i : Instr) (fetch : (program s)[pc]?=some i) :
    (pc<22 ∧ (products s)[pc]?=some i) ∨
    (∃ k<s.depth, ∃ j<16, pc=22+16*k+j ∧ (round s k)[j]?=some i) ∨
    (∃ j<20, pc=22+16*s.depth+j ∧ (output s)[j]?=some i) := by
  have bound : pc<42+16*s.depth := by simpa [program_length] using (List.getElem?_eq_some_iff.mp fetch).choose
  by_cases product : pc<22
  · exact .inl ⟨product,by simpa [program,List.getElem?_append,product,show pc<22+16*s.depth by omega,
      List.length_flatMap,List.sum_replicate,Nat.mul_comm] using fetch⟩
  · by_cases rounds : pc<22+16*s.depth
    · let k := (pc-22)/16
      let j := (pc-22)%16
      have kj : 22+16*k+j=pc := by dsimp [k,j]; omega
      have hk : k<s.depth := by dsimp [k]; omega
      have hj : j<16 := by dsimp [j]; omega
      exact .inr (.inl ⟨k,hk,j,hj,kj.symm,by rw [← round_fetch s k hk j (by simpa using hj),kj]; exact fetch⟩)
    · let j := pc-(22+16*s.depth)
      have hj : j<20 := by dsimp [j]; omega
      have pj : pc=22+16*s.depth+j := by dsimp [j]; omega
      exact .inr (.inr ⟨j,hj,pj,by rw [← output_fetch s j (by simpa using hj),← pj]; exact fetch⟩)

theorem scalar_data (s : Shape) (b : ArithmeticBounds s) (global : List Word) (t : Fin s.threads)
    (a next : Scalar.State) (i : Scalar.Instr) (occ : Scalar.Occurrence) (data : Data s global t a)
    (fetch : (program s)[a.pc]?=some (.localStep i) ∨ ∃ space, (program s)[a.pc]?=some (.memory space i))
    (evaluated : Scalar.eval candidate i a=.next next occ)
    (reads : ∀ effect, occ.memory=some effect → effect.kind=.load → ReadData s global t occ.pc effect.value) :
    Data s global t next := by
  rcases fetch with localFetch | ⟨space,memory⟩
  · rcases program_segment s a.pc _ localFetch with ⟨_,h⟩ | ⟨k,hk,j,hj,site,h⟩ | ⟨j,hj,site,h⟩
    · exact product_scalar_data s b global t a next i occ data (.inl h) evaluated reads
    · exact round_scalar_data s b global t a next i occ k j hk hj site data (.inl h) evaluated reads
    · exact output_scalar_data s b global t a next i occ j hj site data (.inl h) evaluated reads
  · rcases program_segment s a.pc _ memory with ⟨_,h⟩ | ⟨k,hk,j,hj,site,h⟩ | ⟨j,hj,site,h⟩
    · exact product_scalar_data s b global t a next i occ data (.inr ⟨space,h⟩) evaluated reads
    · exact round_scalar_data s b global t a next i occ k j hk hj site data (.inr ⟨space,h⟩) evaluated reads
    · exact output_scalar_data s b global t a next i occ j hj site data (.inr ⟨space,h⟩) evaluated reads

theorem fp_data (s : Shape) (global : List Word) (t : Fin s.threads)
    (a next : Scalar.State) (i : Scalar.Binary32.Instr) (occ : Scalar.Binary32.Occurrence) (data : Data s global t a)
    (fetch : (program s)[a.pc]?=some (.binary32 i)) (evaluated : Scalar.Binary32.Eval i a next occ) :
    Data s global t next := by
  rcases program_segment s a.pc _ fetch with ⟨bound,h⟩ | ⟨k,hk,j,hj,site,h⟩ | ⟨j,hj,site,h⟩
  · interval_cases pc : a.pc <;> simp [products,pointer,scalar,guarded] at h
    subst i
    exact product_fp_data s global t a next occ pc data evaluated
  · interval_cases j <;> simp [round,pointer,scalar,guarded] at h
    subst i
    exact round_fp_data s global t a next occ k hk site data evaluated
  · interval_cases j <;> simp [output,pointer,scalar,guarded] at h
    subst i
    exact output_fp_data s global t a next occ site data evaluated

/-- Releasing a barrier changes only the PC. No live tensor value is reset. -/
theorem barrier_data (s : Shape) (global : List Word) (t : Fin s.threads) (a : Scalar.State)
    (resource : Fin 16) (data : Data s global t a) (fetch : (program s)[a.pc]?=some (.sync resource)) :
    Data s global t {a with pc := a.pc+1} := by
  rcases program_segment s a.pc _ fetch with ⟨bound,h⟩ | ⟨k,hk,j,hj,site,h⟩ | ⟨j,hj,site,h⟩
  · interval_cases pc : a.pc <;> simp [products,pointer,scalar,guarded] at h
    rcases data with ⟨tid,col,pg,inp,wei,prod,rg,left,right,red,og,root,bias,aff,sign,out⟩
    constructor <;> simp only [pc,Nat.reduceAdd] at * <;> intros
    all_goals first | omega | assumption | (apply col; omega)
  · interval_cases j <;> simp [round,pointer,scalar,guarded] at h
    rcases data with ⟨tid,col,pg,inp,wei,prod,rg,left,right,red,og,root,bias,aff,sign,out⟩
    constructor <;> simp only [site,Nat.reduceAdd] at * <;> intros
    all_goals first | omega | assumption | (apply col; omega)
  · interval_cases j <;> simp [output,pointer,scalar,guarded] at h


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


end Ptx.Scalar.Parallel.Dense.Compact

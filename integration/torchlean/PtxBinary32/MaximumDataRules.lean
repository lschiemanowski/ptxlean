import PtxBinary32.MaximumDataStep
import PtxBinary32.MaximumControl

namespace Ptx.Scalar.Parallel.Maximum
open Ptx.Binary32

/-- Classify any fetched instruction into one of the three program segments. -/
theorem program_segment (d : Nat) (pc : Nat) (i : Instr) (fetch : (program d)[pc]?=some i) :
    (pc<6 ∧ publish[pc]?=some i) ∨
    (∃ k<d, ∃ j<24, pc=6+24*k+j ∧ (round d k)[j]?=some i) ∨
    (∃ j<12, pc=6+24*d+j ∧ (output d)[j]?=some i) := by
  have bound : pc<18+24*d := by simpa [program_length] using (List.getElem?_eq_some_iff.mp fetch).choose
  by_cases product : pc<6
  · exact .inl ⟨product,by simpa [program,List.getElem?_append,product,show pc<6+24*d by omega,
      List.length_flatMap,List.sum_replicate,Nat.mul_comm] using fetch⟩
  · by_cases rounds : pc<6+24*d
    · let k := (pc-6)/24
      let j := (pc-6)%24
      have kj : 6+24*k+j=pc := by dsimp [k,j]; omega
      have hk : k<d := by dsimp [k]; omega
      have hj : j<24 := by dsimp [j]; omega
      exact .inr (.inl ⟨k,hk,j,hj,kj.symm,by rw [← round_fetch d k hk j (by simpa using hj),kj]; exact fetch⟩)
    · let j := pc-(6+24*d)
      have hj : j<12 := by dsimp [j]; omega
      have pj : pc=6+24*d+j := by dsimp [j]; omega
      exact .inr (.inr ⟨j,hj,pj,by rw [← output_fetch d j (by simpa using hj),← pj]; exact fetch⟩)

theorem scalar_data (d : Nat) (b : Bounds d) (global : List Word) (t : Fin (width d))
    (a next : Scalar.State) (i : Scalar.Instr) (occ : Scalar.Occurrence) (data : Data d global t a)
    (fetch : (program d)[a.pc]?=some (.localStep i) ∨ ∃ space, (program d)[a.pc]?=some (.memory space i))
    (evaluated : Scalar.eval candidate i a=.next next occ)
    (reads : ∀ effect, occ.memory=some effect → effect.kind=.load → ReadData d global t occ.pc effect.value) :
    Data d global t next := by
  rcases fetch with localFetch | ⟨space,memory⟩
  · rcases program_segment d a.pc _ localFetch with ⟨_,h⟩ | ⟨k,hk,j,hj,site,h⟩ | ⟨j,hj,site,h⟩
    · exact publish_scalar_data d b global t a next i occ data (.inl h) evaluated reads
    · exact round_scalar_data d b global t a next i occ k j hk hj site data (.inl h) evaluated reads
    · exact output_scalar_data d b global t a next i occ j hj site data (.inl h) evaluated reads
  · rcases program_segment d a.pc _ memory with ⟨_,h⟩ | ⟨k,hk,j,hj,site,h⟩ | ⟨j,hj,site,h⟩
    · exact publish_scalar_data d b global t a next i occ data (.inr ⟨space,h⟩) evaluated reads
    · exact round_scalar_data d b global t a next i occ k j hk hj site data (.inr ⟨space,h⟩) evaluated reads
    · exact output_scalar_data d b global t a next i occ j hj site data (.inr ⟨space,h⟩) evaluated reads

theorem no_fp (d : Nat) (pc : Nat) (i : Scalar.Binary32.Instr)
    (fetch : (program d)[pc]?=some (.binary32 i)) : False := by
  rcases program_segment d pc _ fetch with ⟨bound,h⟩ | ⟨k,hk,j,hj,site,h⟩ | ⟨j,hj,site,h⟩
  · interval_cases pc <;> simp [publish,publishCode,Dense.pointer,Dense.scalar,Dense.guarded] at h
  · interval_cases j <;> simp [round,roundCode,roundPrefix,roundSuffix,Scalar.MaximumSelect.code,Dense.pointer,Dense.scalar,Dense.guarded] at h
  · interval_cases j <;> simp [output,outputCode,Dense.pointer,Dense.scalar,Dense.guarded] at h

/-- Releasing a barrier changes only the PC. No live tensor value is reset. -/
theorem barrier_data (d : Nat) (global : List Word) (t : Fin (width d)) (a : Scalar.State)
    (resource : Fin 16) (data : Data d global t a) (fetch : (program d)[a.pc]?=some (.sync resource)) :
    Data d global t {a with pc := a.pc+1} := by
  rcases program_segment d a.pc _ fetch with ⟨bound,h⟩ | ⟨k,hk,j,hj,site,h⟩ | ⟨j,hj,site,h⟩
  · interval_cases pc : a.pc <;> simp [publish,publishCode,Dense.pointer,Dense.scalar,Dense.guarded] at h
    rcases data with ⟨tid,pub,rg,left,right,ls,lr,lk,rs,rr,rk,cmp,sl,red,og,root⟩
    constructor <;> simp only [pc,Nat.reduceAdd] at * <;> intros
    all_goals first | omega | assumption
  · interval_cases j <;> simp [round,roundCode,roundPrefix,roundSuffix,Scalar.MaximumSelect.code,Dense.pointer,Dense.scalar,Dense.guarded] at h
    rcases data with ⟨tid,pub,rg,left,right,ls,lr,lk,rs,rr,rk,cmp,sl,red,og,root⟩
    constructor <;> simp only [site,Nat.reduceAdd] at * <;> intros
    all_goals first | omega | assumption
  · interval_cases j <;> simp [output,outputCode,Dense.pointer,Dense.scalar,Dense.guarded] at h

end Ptx.Scalar.Parallel.Maximum

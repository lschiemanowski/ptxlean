import PtxBinary32.DenseDataStep
import PtxBinary32.DenseDataFP

namespace Ptx.Scalar.Parallel.Dense
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

end Ptx.Scalar.Parallel.Dense

import PtxBinary32.CompactDenseProgram
import PtxBinary32.DenseLoadSites

/-! Compact per-group dense scratch. Arithmetic contracts are shared with Dense;
only the fetched shared addresses and their allocation change. -/
namespace Ptx.Scalar.Parallel.Dense.Compact
theorem program_straight (s : Shape) : Control.Straight (program s) := by
  intro i member
  simp only [program,List.mem_append,List.mem_flatMap,List.mem_range] at member
  rcases member with (first | ⟨k,hk,roundMem⟩) | last
  · simp [products,pointer] at first
    rcases first with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals trivial
  · simp [round,pointer] at roundMem
    rcases roundMem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals trivial
  · simp [output,pointer] at last
    rcases last with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals trivial

private theorem products_store_site (s : Shape) (pc : Nat) (space : Space) (i : Scalar.Instr)
    (fetch : (products s)[pc]? = some (.memory space i))
    (store : Memory.Prior.memoryKind i.op = some .store) : pc=20 ∧ space=.shared := by
  have bound : pc<22 := by simpa using (List.getElem?_eq_some_iff.mp fetch).choose
  interval_cases pc <;> simp_all [products,pointer,scalar,guarded,Memory.Prior.memoryKind,
    Ptx.Scalar.SharedReduction.Machine.Control.memoryKind,Scalar.Instr.plain]
  all_goals obtain ⟨_,rfl⟩ := fetch; contradiction

private theorem round_store_site (s : Shape) (k pc : Nat) (space : Space) (i : Scalar.Instr)
    (fetch : (round s k)[pc]? = some (.memory space i))
    (store : Memory.Prior.memoryKind i.op = some .store) : pc=14 ∧ space=.shared := by
  have bound : pc<16 := by simpa using (List.getElem?_eq_some_iff.mp fetch).choose
  interval_cases pc <;> simp_all [round,pointer,scalar,guarded,Memory.Prior.memoryKind,
    Ptx.Scalar.SharedReduction.Machine.Control.memoryKind,Scalar.Instr.plain]
  all_goals obtain ⟨_,rfl⟩ := fetch; contradiction

private theorem output_store_site (s : Shape) (pc : Nat) (space : Space) (i : Scalar.Instr)
    (fetch : (output s)[pc]? = some (.memory space i))
    (store : Memory.Prior.memoryKind i.op = some .store) : pc=18 ∧ space=.global := by
  have bound : pc<20 := by simpa using (List.getElem?_eq_some_iff.mp fetch).choose
  interval_cases pc <;> simp_all [output,pointer,scalar,guarded,Memory.Prior.memoryKind,
    Ptx.Scalar.SharedReduction.Machine.Control.memoryKind,Scalar.Instr.plain]
  all_goals obtain ⟨_,rfl⟩ := fetch; contradiction

/-- Exhaustive store-site classification of the actual instruction list. -/
theorem fetched_store_site (s : Shape) (pc : Nat) (space : Space) (i : Scalar.Instr)
    (fetch : (program s)[pc]? = some (.memory space i))
    (store : Memory.Prior.memoryKind i.op = some .store) :
    (pc=20 ∧ space=.shared) ∨
    (∃ k, k<s.depth ∧ pc=22+16*k+14 ∧ space=.shared) ∨
    (pc=22+16*s.depth+18 ∧ space=.global) := by
  have bound : pc<42+16*s.depth := by simpa [program_length] using (List.getElem?_eq_some_iff.mp fetch).choose
  by_cases product : pc<22
  · left
    apply products_store_site s pc space i _ store
    simpa [program,List.getElem?_append,product,show pc<22+16*s.depth by omega,
      List.length_flatMap,List.sum_replicate,Nat.mul_comm] using fetch
  · by_cases rounds : pc<22+16*s.depth
    · let k := (pc-22)/16
      let j := (pc-22)%16
      have kj : 22+16*k+j=pc := by dsimp [k,j]; omega
      have hk : k<s.depth := by dsimp [k]; omega
      have hj : j<(round s k).length := by rw [round_length]; dsimp [j]; omega
      have atJ : (round s k)[j]? = some (.memory space i) := by
        rw [← round_fetch s k hk j hj,kj]; exact fetch
      obtain ⟨siteEq,which⟩ := round_store_site s k j space i atJ store
      exact .inr (.inl ⟨k,hk,by omega,which⟩)
    · have jbound : pc-(22+16*s.depth)<(output s).length := by rw [output_length]; omega
      have atJ : (output s)[pc-(22+16*s.depth)]? = some (.memory space i) := by
        rw [← output_fetch s (pc-(22+16*s.depth)) jbound,show 22+16*s.depth+(pc-(22+16*s.depth))=pc by omega]
        exact fetch
      obtain ⟨siteEq,which⟩ := output_store_site s _ space i atJ store
      exact .inr (.inr ⟨by omega,which⟩)

/-- Every emitted store, including in incomplete candidate runs, comes from one
of the classified sites. This is stronger than inspecting the selected runner. -/
private theorem product_load_site (s : Shape) (pc : Nat) (space : Space) (i : Scalar.Instr)
    (fetch : (products s)[pc]?=some (.memory space i)) (load : Memory.Prior.memoryKind i.op=some .load) :
    ∃ weight : Bool, pc=(if weight then 15 else 11) ∧ space=.global ∧ i=productLoad weight := by
  have bound : pc<22 := by simpa using (List.getElem?_eq_some_iff.mp fetch).choose
  interval_cases pc <;> simp_all [products,pointer,scalar,guarded,Memory.Prior.memoryKind,
    Ptx.Scalar.SharedReduction.Machine.Control.memoryKind,Scalar.Instr.plain,productLoad,Bool.exists_bool]
  all_goals obtain ⟨_,rfl⟩ := fetch; contradiction

private theorem round_load_site (s : Shape) (k pc : Nat) (space : Space) (i : Scalar.Instr)
    (fetch : (round s k)[pc]?=some (.memory space i)) (load : Memory.Prior.memoryKind i.op=some .load) :
    ∃ right : Bool, pc=(if right then 8 else 7) ∧ space=.shared ∧ i=roundLoad right := by
  have bound : pc<16 := by simpa using (List.getElem?_eq_some_iff.mp fetch).choose
  interval_cases pc <;> simp_all [round,pointer,scalar,guarded,Memory.Prior.memoryKind,
    Ptx.Scalar.SharedReduction.Machine.Control.memoryKind,Scalar.Instr.plain,roundLoad,Bool.exists_bool]
  all_goals obtain ⟨_,rfl⟩ := fetch; contradiction

private theorem output_load_site (s : Shape) (pc : Nat) (space : Space) (i : Scalar.Instr)
    (fetch : (output s)[pc]?=some (.memory space i)) (load : Memory.Prior.memoryKind i.op=some .load) :
    ∃ bias : Bool, pc=(if bias then 10 else 5) ∧ space=(if bias then .global else .shared) ∧ i=outputLoad bias := by
  have bound : pc<20 := by simpa using (List.getElem?_eq_some_iff.mp fetch).choose
  interval_cases pc <;> simp_all [output,pointer,scalar,guarded,Memory.Prior.memoryKind,
    Ptx.Scalar.SharedReduction.Machine.Control.memoryKind,Scalar.Instr.plain,outputLoad,Bool.exists_bool]
  all_goals obtain ⟨_,rfl⟩ := fetch; contradiction

theorem fetched_load_site (s : Shape) (pc : Nat) (space : Space) (i : Scalar.Instr)
    (fetch : (program s)[pc]?=some (.memory space i)) (load : Memory.Prior.memoryKind i.op=some .load) :
    (∃ weight : Bool, pc=(if weight then 15 else 11) ∧ space=.global ∧ i=productLoad weight) ∨
    (∃ k, k<s.depth ∧ ∃ right : Bool, pc=22+16*k+(if right then 8 else 7) ∧ space=.shared ∧ i=roundLoad right) ∨
    (∃ bias : Bool, pc=22+16*s.depth+(if bias then 10 else 5) ∧ space=(if bias then .global else .shared) ∧ i=outputLoad bias) := by
  have bound : pc<42+16*s.depth := by simpa [program_length] using (List.getElem?_eq_some_iff.mp fetch).choose
  by_cases product : pc<22
  · left
    apply product_load_site s pc space i _ load
    simpa [program,List.getElem?_append,product,show pc<22+16*s.depth by omega,
      List.length_flatMap,List.sum_replicate,Nat.mul_comm] using fetch
  · by_cases rounds : pc<22+16*s.depth
    · let k := (pc-22)/16
      let j := (pc-22)%16
      have kj : 22+16*k+j=pc := by dsimp [k,j]; omega
      have hk : k<s.depth := by dsimp [k]; omega
      have hj : j<(round s k).length := by rw [round_length]; dsimp [j]; omega
      have atJ : (round s k)[j]?=some (.memory space i) := by rw [← round_fetch s k hk j hj,kj]; exact fetch
      obtain ⟨right,site,sp,inst⟩ := round_load_site s k j space i atJ load
      exact .inr (.inl ⟨k,hk,right,by omega,sp,inst⟩)
    · have hj : pc-(22+16*s.depth)<(output s).length := by rw [output_length]; omega
      have atJ : (output s)[pc-(22+16*s.depth)]?=some (.memory space i) := by
        rw [← output_fetch s _ hj,show 22+16*s.depth+(pc-(22+16*s.depth))=pc by omega]; exact fetch
      obtain ⟨bias,site,sp,inst⟩ := output_load_site s _ space i atJ load
      exact .inr (.inr ⟨bias,by omega,sp,inst⟩)

theorem fetched_exit_site (s : Shape) (pc : Nat) (fetch : (program s)[pc]?=some .exit) :
    pc=22+16*s.depth+19 := by
  have bound : pc<42+16*s.depth := by simpa [program_length] using (List.getElem?_eq_some_iff.mp fetch).choose
  by_cases product : pc<22
  · have atP : (products s)[pc]?=some .exit := by
      simpa [program,List.getElem?_append,product,show pc<22+16*s.depth by omega,
        List.length_flatMap,List.sum_replicate,Nat.mul_comm] using fetch
    have member := List.mem_of_getElem? atP
    simp [products,pointer,scalar,guarded] at member
  · by_cases rounds : pc<22+16*s.depth
    · let k := (pc-22)/16
      let j := (pc-22)%16
      have kj : 22+16*k+j=pc := by dsimp [k,j]; omega
      have hk : k<s.depth := by dsimp [k]; omega
      have hj : j<(round s k).length := by rw [round_length]; dsimp [j]; omega
      have atJ : (round s k)[j]?=some .exit := by rw [← round_fetch s k hk j hj,kj]; exact fetch
      have member := List.mem_of_getElem? atJ
      simp [round,pointer,scalar,guarded] at member
    · have jb : pc-(22+16*s.depth)<20 := by omega
      have atJ : (output s)[pc-(22+16*s.depth)]?=some .exit := by
        rw [← output_fetch s _ (by simpa using jb),show 22+16*s.depth+(pc-(22+16*s.depth))=pc by omega]
        exact fetch
      have index : pc-(22+16*s.depth)=19 := by
        generalize pc-(22+16*s.depth)=j at atJ jb ⊢
        interval_cases j <;> simp_all [output,pointer,scalar,guarded]
      omega

end Ptx.Scalar.Parallel.Dense.Compact

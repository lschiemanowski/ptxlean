import PtxBinary32.DenseLoadControl

/-! Exhaustive load-site classification, retaining the concrete operand and guard. -/
namespace Ptx.Scalar.Parallel.Dense

def productLoad (weight : Bool) : Scalar.Instr :=
  ⟨.pred 0 true,.load (if weight then 5 else 4) (.reg (if weight then 1 else 0))⟩
def roundLoad (right : Bool) : Scalar.Instr :=
  ⟨.pred 0 true,.load (if right then 5 else 4) (.reg (if right then 4 else 3))⟩
def outputLoad (bias : Bool) : Scalar.Instr :=
  ⟨.pred 0 true,.load (if bias then 8 else 6) (.reg (if bias then 5 else 2))⟩

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

/-- Addresses and active predicates are consequences of actual emitted loads. -/
theorem candidate_load_address (s : Shape) (b : Bounds s) (global shared : List Word)
    (seeds : Fin s.threads → Scalar.State) {events : List (Event s.threads)} {final : Parallel.State s.threads}
    (run : Runs (config s b) (program s) (initial s global shared seeds) events final)
    (t : Fin s.threads) (space : Space) (occ : Scalar.Occurrence) (effect : MemoryEffect)
    (member : .scalar t (some space) occ ∈ events) (memory : occ.memory=some effect) (load : effect.kind=.load) :
    (∃ weight : Bool, occ.pc=(if weight then 15 else 11) ∧ space=.global ∧ t.val%s.width<s.columns ∧
      effect.address=bytePointer (if weight then s.weight (t.val/s.width) (t.val%s.width) else t.val%s.width)) ∨
    (∃ k, k<s.depth ∧ ∃ right : Bool, occ.pc=22+16*k+(if right then 8 else 7) ∧ space=.shared ∧
      t.val%s.width<2^(s.depth-(k+1)) ∧ effect.address=bytePointer (leftIndex s k t+if right then 1 else 0)) ∨
    (∃ bias : Bool, occ.pc=22+16*s.depth+(if bias then 10 else 5) ∧ space=(if bias then .global else .shared) ∧
      t.val%s.width=0 ∧ effect.address=bytePointer (if bias then biasIndex s t else rootIndex s t)) := by
  have access := Memory.run_access_complete run member memory
  have conditions : (program s)[occ.pc]?=some (.memory space occ.instruction) ∧
      occ.executed=true ∧ Memory.Prior.memoryKind occ.instruction.op=some effect.kind := by
    simpa [Memory.access,memory] using access
  obtain ⟨destination,address,op,addr,gate⟩ := AddressControl.run_load run (program_address_compatible s)
    (initial_address_control s global shared seeds) (reset_aligned _ _ _ _) member memory load
  rcases fetched_load_site s occ.pc space occ.instruction conditions.1 (by simpa [load] using conditions.2.2) with
    ⟨weight,site,sp,inst⟩ | ⟨k,hk,right,site,sp,inst⟩ | ⟨bias,site,sp,inst⟩
  · have operands := Scalar.Op.load.inj (inst ▸ op).symm
    have control := product_read_control s b seeds t weight
    have enabled := gate (by rw [inst]; rfl)
    rw [site,control.2] at enabled
    rw [operands.2] at addr
    exact .inl ⟨weight,site,sp,by simpa using enabled,by simpa [Scalar.Operand64.eval,site,control.1] using addr⟩
  · have operands := Scalar.Op.load.inj (inst ▸ op).symm
    have control := round_read_control s b seeds t k hk right
    have enabled := gate (by rw [inst]; rfl)
    rw [site,control.2] at enabled
    rw [operands.2] at addr
    exact .inr (.inl ⟨k,hk,right,site,sp,by simpa using enabled,by simpa [Scalar.Operand64.eval,site,control.1] using addr⟩)
  · have operands := Scalar.Op.load.inj (inst ▸ op).symm
    have control := output_read_control s b seeds t bias
    have enabled := gate (by rw [inst]; rfl)
    rw [site,control.2] at enabled
    rw [operands.2] at addr
    exact .inr (.inr ⟨bias,site,sp,by simpa using enabled,by simpa [Scalar.Operand64.eval,site,control.1] using addr⟩)

end Ptx.Scalar.Parallel.Dense

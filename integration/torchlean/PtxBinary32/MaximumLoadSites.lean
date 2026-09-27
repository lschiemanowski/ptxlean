import PtxBinary32.MaximumLoadControl

/-! Exhaustive load-site classification of the fetched maximum program. -/
namespace Ptx.Scalar.Parallel.Maximum

def publicationLoad : Scalar.Instr := .plain (.load 4 (.reg 0))
def roundLoad (right : Bool) : Scalar.Instr :=
  ⟨.pred 0 true,.load (if right then 5 else 4) (.reg (if right then 2 else 1))⟩
def outputLoad : Scalar.Instr := ⟨.pred 0 true,.load 6 (.reg 0)⟩

private theorem publication_load_site (pc : Nat) (space : Space) (i : Scalar.Instr)
    (fetch : publish[pc]?=some (.memory space i)) (load : Memory.Prior.memoryKind i.op=some .load) :
    pc=3 ∧ space=.global ∧ i=publicationLoad := by
  have bound : pc<6 := by simpa using (List.getElem?_eq_some_iff.mp fetch).choose
  interval_cases pc <;> simp_all [publish,publishCode,pointer,Dense.pointer,Dense.scalar,Memory.Prior.memoryKind,
    Ptx.Scalar.SharedReduction.Machine.Control.memoryKind,Scalar.Instr.plain,publicationLoad]
  all_goals obtain ⟨rfl,rfl⟩ := fetch
  all_goals simp_all [Memory.Prior.memoryKind]

private theorem round_load_site (d k pc : Nat) (space : Space) (i : Scalar.Instr)
    (fetch : (round d k)[pc]?=some (.memory space i)) (load : Memory.Prior.memoryKind i.op=some .load) :
    ∃ right : Bool, pc=(if right then 8 else 7) ∧ space=.shared ∧ i=roundLoad right := by
  have bound : pc<24 := by simpa using (List.getElem?_eq_some_iff.mp fetch).choose
  interval_cases pc <;> simp_all [round,roundCode,roundPrefix,roundSuffix,Scalar.MaximumSelect.code,pointer,Dense.pointer,scalar,Dense.scalar,guarded,Dense.guarded,Memory.Prior.memoryKind,
    Ptx.Scalar.SharedReduction.Machine.Control.memoryKind,Scalar.Instr.plain,roundLoad,Bool.exists_bool]
  all_goals obtain ⟨rfl,rfl⟩ := fetch
  all_goals simp_all [Memory.Prior.memoryKind]

private theorem output_load_site (d pc : Nat) (space : Space) (i : Scalar.Instr)
    (fetch : (output d)[pc]?=some (.memory space i)) (load : Memory.Prior.memoryKind i.op=some .load) :
    pc=5 ∧ space=.shared ∧ i=outputLoad := by
  have bound : pc<12 := by simpa using (List.getElem?_eq_some_iff.mp fetch).choose
  interval_cases pc <;> simp_all [output,outputCode,pointer,Dense.pointer,scalar,Dense.scalar,guarded,Dense.guarded,Memory.Prior.memoryKind,
    Ptx.Scalar.SharedReduction.Machine.Control.memoryKind,Scalar.Instr.plain,outputLoad]
  all_goals obtain ⟨rfl,rfl⟩ := fetch
  all_goals simp_all [Memory.Prior.memoryKind]

theorem fetched_load_site (d pc : Nat) (space : Space) (i : Scalar.Instr)
    (fetch : (program d)[pc]?=some (.memory space i)) (load : Memory.Prior.memoryKind i.op=some .load) :
    (pc=3 ∧ space=.global ∧ i=publicationLoad) ∨
    (∃ k, k<d ∧ ∃ right : Bool, pc=6+24*k+(if right then 8 else 7) ∧ space=.shared ∧ i=roundLoad right) ∨
    (pc=6+24*d+5 ∧ space=.shared ∧ i=outputLoad) := by
  have bound : pc<18+24*d := by simpa [program_length] using (List.getElem?_eq_some_iff.mp fetch).choose
  by_cases publication : pc<6
  · left
    apply publication_load_site pc space i _ load
    simpa [program,List.getElem?_append,publication,show pc<6+24*d by omega,
      List.length_flatMap,List.sum_replicate,Nat.mul_comm] using fetch
  · by_cases rounds : pc<6+24*d
    · let k := (pc-6)/24
      let j := (pc-6)%24
      have kj : 6+24*k+j=pc := by dsimp [k,j]; omega
      have hk : k<d := by dsimp [k]; omega
      have hj : j<(round d k).length := by rw [round_length]; dsimp [j]; omega
      have atJ : (round d k)[j]?=some (.memory space i) := by rw [←round_fetch d k hk j hj,kj]; exact fetch
      obtain ⟨right,site,sp,inst⟩ := round_load_site d k j space i atJ load
      exact .inr (.inl ⟨k,hk,right,by omega,sp,inst⟩)
    · have hj : pc-(6+24*d)<(output d).length := by rw [output_length]; omega
      have atJ : (output d)[pc-(6+24*d)]?=some (.memory space i) := by
        rw [←output_fetch d _ hj,show 6+24*d+(pc-(6+24*d))=pc by omega]; exact fetch
      obtain ⟨site,sp,inst⟩ := output_load_site d _ space i atJ load
      exact .inr (.inr ⟨by omega,sp,inst⟩)

/-- Every emitted address and lane predicate follows from the real instructions. -/
theorem candidate_load_address (d : Nat) (b : Bounds d) (global shared : List Word)
    (seeds : Fin (width d)→Scalar.State) {events : List (Event (width d))} {final : Parallel.State (width d)}
    (run : Runs (config d) (program d) (initial d global shared seeds) events final)
    (t : Fin (width d)) (space : Space) (occ : Scalar.Occurrence) (effect : MemoryEffect)
    (member : .scalar t (some space) occ ∈ events) (memory : occ.memory=some effect) (load : effect.kind=.load) :
    (occ.pc=3 ∧ space=.global ∧ effect.address=bytePointer t.val) ∨
    (∃ k, k<d ∧ ∃ right : Bool, occ.pc=6+24*k+(if right then 8 else 7) ∧ space=.shared ∧
      t.val<2^(d-(k+1)) ∧ effect.address=bytePointer (k*width d+2*t.val+if right then 1 else 0)) ∨
    (occ.pc=6+24*d+5 ∧ space=.shared ∧ t.val=0 ∧ effect.address=bytePointer (d*width d)) := by
  have access := Memory.run_access_complete run member memory
  have conditions : (program d)[occ.pc]?=some (.memory space occ.instruction) ∧
      occ.executed=true ∧ Memory.Prior.memoryKind occ.instruction.op=some effect.kind := by
    simpa [Memory.access,memory] using access
  obtain ⟨destination,address,op,addr,gate⟩ := AddressControl.run_load run (program_address_compatible d)
    (initial_address_control d global shared seeds) (reset_aligned _ _ _ _) member memory load
  rcases fetched_load_site d occ.pc space occ.instruction conditions.1 (by simpa [load] using conditions.2.2) with
    ⟨site,sp,inst⟩ | ⟨k,hk,right,site,sp,inst⟩ | ⟨site,sp,inst⟩
  · have operands := Scalar.Op.load.inj (inst ▸ op).symm
    have control := publication_read_control b seeds t
    rw [operands.2] at addr
    exact .inl ⟨site,sp,by simpa [Scalar.Operand64.eval,site,control] using addr⟩
  · have operands := Scalar.Op.load.inj (inst ▸ op).symm
    have control := round_read_control b seeds t k hk right
    have enabled := gate (by rw [inst]; rfl)
    rw [site,control.2] at enabled
    rw [operands.2] at addr
    exact .inr (.inl ⟨k,hk,right,site,sp,by simpa using enabled,by simpa [Scalar.Operand64.eval,site,control.1] using addr⟩)
  · have operands := Scalar.Op.load.inj (inst ▸ op).symm
    have control := output_read_control b seeds t
    have enabled := gate (by rw [inst]; rfl)
    rw [site,control.2] at enabled
    rw [operands.2] at addr
    exact .inr (.inr ⟨site,sp,by simpa using enabled,by simpa [Scalar.Operand64.eval,site,control.1] using addr⟩)

end Ptx.Scalar.Parallel.Maximum

import PtxBinary32.PointwiseProgram

namespace Ptx.Scalar.Parallel.Pointwise

theorem compatible (op : Op) : AddressControl.ProgramCompatible (program op) := by
  intro i member
  cases op <;> simp [program,body,localOp,clear] at member
  all_goals repeat' (first | (rcases member with rfl | member) | (subst i))
  all_goals simp [AddressControl.Compatible,AddressControl.Allowed,AddressControl.Visible,Scalar.Instr.plain,localOp,clear]

private theorem instruction_addresses (op : Op) (i : Instr) (member : i ∈ program op) (a : Scalar.State) :
    (AddressControl.instruction i a).addrs=a.addrs := by
  cases op <;> simp [program,body,localOp,clear] at member
  all_goals repeat' (first | (rcases member with rfl | member) | (subst i))
  all_goals rfl

private theorem evaluate_addresses (op : Op) (code : List Instr) (part : ∀ i ∈ code, i ∈ program op)
    (a : Scalar.State) : (AddressControl.evaluate code a).addrs=a.addrs := by
  induction code generalizing a with
  | nil => rfl
  | cons i rest ih =>
    change (AddressControl.evaluate rest (AddressControl.instruction i a)).addrs=a.addrs
    rw [ih (fun j hj => part j (by simp [hj]))]
    exact instruction_addresses op i (part i (by simp)) a

theorem control_addresses (op : Op) (a : Scalar.State) (pc : Nat) :
    (AddressControl.atPC (program op) a pc).addrs=a.addrs :=
  evaluate_addresses op _ (fun _ h => List.mem_of_mem_take h) a

theorem initial_control (op : Op) (l : Layout n) (global shared : List Word) (seeds : Fin n → Scalar.State) :
    AddressControl.Invariant (program op) (seed l seeds) (initial l global shared seeds) := by
  intro t
  exact AddressControl.agree_refl _

theorem initial_aligned (l : Layout n) (global shared : List Word) (seeds : Fin n → Scalar.State) :
    Aligned (initial l global shared seeds) := by
  intro t h; simp [initial,Barrier.reset] at h

theorem fetched_load (op : Op) (pc : Nat) (space : Space) (i : Scalar.Instr)
    (fetch : (program op)[pc]?=some (.memory space i)) (load : Memory.Prior.memoryKind i.op=some .load) :
    space=.global ∧ ∃ right : Bool, pc=(if right then 1 else 0) ∧
      i=.plain (.load (if right then 5 else 4) (.reg (if right then 1 else 0))) := by
  have bound : pc<(program op).length := (List.getElem?_eq_some_iff.mp fetch).choose
  cases op <;> simp [program,body,localOp,clear] at bound
  all_goals interval_cases pc <;> simp_all [program,body,localOp,clear,Bool.exists_bool,Memory.Prior.memoryKind,
    Ptx.Scalar.SharedReduction.Machine.Control.memoryKind,Scalar.Instr.plain]
  all_goals obtain ⟨_,rfl⟩ := fetch; contradiction

theorem fetched_store (op : Op) (pc : Nat) (space : Space) (i : Scalar.Instr)
    (fetch : (program op)[pc]?=some (.memory space i)) (store : Memory.Prior.memoryKind i.op=some .store) :
    space=.global ∧ pc=storePC op ∧ i=.plain (.store (.reg 2) (.reg 6)) := by
  have bound : pc<(program op).length := (List.getElem?_eq_some_iff.mp fetch).choose
  cases op <;> simp [program,body,localOp,clear] at bound
  all_goals interval_cases pc <;> simp_all [program,body,localOp,clear,storePC,Memory.Prior.memoryKind,
    Ptx.Scalar.SharedReduction.Machine.Control.memoryKind,Scalar.Instr.plain]
  all_goals obtain ⟨_,rfl⟩ := fetch; contradiction

theorem load_address (op : Op) (l : Layout n) (global shared : List Word) (seeds : Fin n → Scalar.State)
    {cfg : Config n} {events : List (Event n)} {final : State n}
    (run : Runs cfg (program op) (initial l global shared seeds) events final)
    (t : Fin n) (space : Space) (occ : Scalar.Occurrence) (effect : MemoryEffect)
    (member : .scalar t (some space) occ ∈ events) (memory : occ.memory=some effect) (load : effect.kind=.load) :
    space=.global ∧ ∃ right : Bool, occ.pc=(if right then 1 else 0) ∧
      effect.address=Dense.bytePointer (if right then l.right t else l.left t) := by
  have access := Memory.run_access_complete run member memory
  have conditions : (program op)[occ.pc]?=some (.memory space occ.instruction) ∧
      occ.executed=true ∧ Memory.Prior.memoryKind occ.instruction.op=some effect.kind := by
    simpa [Memory.access,memory] using access
  obtain ⟨sp,right,pc,inst⟩ := fetched_load op occ.pc space occ.instruction conditions.1 (by simpa [load] using conditions.2.2)
  obtain ⟨destination,address,instruction,addr,_⟩ := AddressControl.run_load run (compatible op)
    (initial_control op l global shared seeds) (initial_aligned l global shared seeds) member memory load
  have operands := Scalar.Op.load.inj (inst ▸ instruction).symm
  rw [operands.2] at addr
  refine ⟨sp,right,pc,?_⟩
  cases right <;> simpa [Scalar.Operand64.eval,control_addresses,seed] using addr

theorem store_address (op : Op) (l : Layout n) (global shared : List Word) (seeds : Fin n → Scalar.State)
    {cfg : Config n} {events : List (Event n)} {final : State n}
    (run : Runs cfg (program op) (initial l global shared seeds) events final)
    (t : Fin n) (space : Space) (occ : Scalar.Occurrence) (effect : MemoryEffect)
    (member : .scalar t (some space) occ ∈ events) (memory : occ.memory=some effect) (store : effect.kind=.store) :
    space=.global ∧ occ.pc=storePC op ∧ effect.address=Dense.bytePointer (l.output t) := by
  have access := Memory.run_access_complete run member memory
  have conditions : (program op)[occ.pc]?=some (.memory space occ.instruction) ∧
      occ.executed=true ∧ Memory.Prior.memoryKind occ.instruction.op=some effect.kind := by
    simpa [Memory.access,memory] using access
  obtain ⟨sp,pc,inst⟩ := fetched_store op occ.pc space occ.instruction conditions.1 (by simpa [store] using conditions.2.2)
  obtain ⟨address,value,instruction,addr,_⟩ := AddressControl.run_store run (compatible op)
    (initial_control op l global shared seeds) (initial_aligned l global shared seeds) member memory store
  have operands := Scalar.Op.store.inj (inst ▸ instruction).symm
  rw [operands.1] at addr
  exact ⟨sp,pc,by simpa [Scalar.Operand64.eval,control_addresses,seed] using addr⟩

end Ptx.Scalar.Parallel.Pointwise

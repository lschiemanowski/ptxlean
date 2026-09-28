import PoissonPTX.Machine

namespace PtxTorchLean.Poisson.PTX

/-- Register numbers used by the PTX frontend: base, widened offset, address,
then floating-point registers and the vector's global index. -/
def wide (s : State) (index : Nat) : Word :=
  BitVec.ofNat 64 ((s.regs index).toNat % 2^32 * 8)

def address (s : State) (index : Nat) (offset : Word) : Word :=
  s.regs 0 + wide s index + offset

def addressCode (index : Nat) (offset : Word) : List Op :=
  [.wide8 1 (.reg index), .add64 2 (.reg 0) (.reg 1), .add64 2 (.reg 2) (.imm offset)]

def addressed (s : State) (index : Nat) (offset : Word) : State :=
  assign (assign (assign s 1 (wide s index)) 2 (s.regs 0+wide s index)) 2 (address s index offset)

def loadCode (dst index : Nat) (offset : Word) : List Op :=
  addressCode index offset ++ [.load64 .global dst (.reg 2)]

def storeCode (src index : Nat) (offset : Word) : List Op :=
  addressCode index offset ++ [.store64 .global (.reg 2) (.reg src)]

@[simp] theorem addressed_memory (s : State) (index : Nat) (offset : Word) :
    (addressed s index offset).global = s.global ∧
    (addressed s index offset).shared = s.shared ∧
    (addressed s index offset).globalBytes = s.globalBytes ∧
    (addressed s index offset).sharedBytes = s.sharedBytes := by
  simp [addressed,assign,advance]

@[simp] theorem addressed_globalStart : (addressed s index offset).globalStart = s.globalStart := rfl
@[simp] theorem addressed_sharedStart : (addressed s index offset).sharedStart = s.sharedStart := rfl

@[simp] theorem addressed_reg (s : State) (index : Nat) (offset : Word) (r : Nat)
    (h1 : r ≠ 1) (h2 : r ≠ 2) : (addressed s index offset).regs r = s.regs r := by
  simp [addressed,assign,advance,h1,h2]

@[simp] theorem addressed_addr (s : State) (index : Nat) (offset : Word) :
    (addressed s index offset).regs 2 = address s index offset := by simp [addressed,assign]

theorem address_run (s : State) (index : Nat) (offset : Word) :
    run (addressCode index offset) s = some (addressed s index offset) := by
  simp [addressCode,run,eval,Operand.eval,addressed,assign,advance,wide,address]

theorem run_append (left right : List Op) (s : State) :
    run (left++right) s = run left s >>= run right := by
  induction left generalizing s with
  | nil => rfl
  | cons op ops ih => cases he : eval op s <;> simp [run,he,ih]

theorem load_run (s : State) (dst index : Nat) (offset : Word)
    (valid : Valid64 s.globalStart s.globalBytes (address s index offset).toNat) :
    run (loadCode dst index offset) s = some
      (assign (addressed s index offset) dst (read64 s.global (address s index offset).toNat)) := by
  simp [loadCode,run_append,address_run,run,eval,Operand.eval,
    State.start,State.bytes,State.memory,valid,addressed_memory]

theorem store_run (s : State) (src index : Nat) (offset : Word)
    (h1 : src ≠ 1) (h2 : src ≠ 2)
    (valid : Valid64 s.globalStart s.globalBytes (address s index offset).toNat) :
    run (storeCode src index offset) s = some
      (put (addressed s index offset) .global (address s index offset).toNat (s.regs src)) := by
  simp [storeCode,run_append,address_run,run,eval,Operand.eval,State.start,State.bytes,valid,h1,h2]

/-- Each byte read lies inside the allocation; address arithmetic has not been
replaced by an assumed scalar stream. -/
theorem load_access_bound (valid : Valid64 start bytes (address s index offset).toNat)
    (k : Fin 8) : (address s index offset).toNat+k.val < start+bytes := by
  have hk := k.isLt; rcases valid with ⟨_,_,_,_⟩; omega

/-- Exact correspondence of an eight-byte PTX load to its decoded scalar value. -/
theorem load_value (s : State) (dst index : Nat) (offset : Word)
    (valid : Valid64 s.globalStart s.globalBytes (address s index offset).toNat) :
    ∃ t, Block (loadCode dst index offset) s t ∧
      decode (t.regs dst) = decode (read64 s.global (address s index offset).toNat) ∧
      t.global = s.global ∧ t.shared = s.shared := by
  refine ⟨_,run_sound (load_run s dst index offset valid),?_,?_,?_⟩
  · simp [assign]
  · rfl
  · rfl

theorem load_block_eq (h : Block (loadCode dst index offset) s t)
    (valid : Valid64 s.globalStart s.globalBytes (address s index offset).toNat) :
    t = assign (addressed s index offset) dst (read64 s.global (address s index offset).toNat) := by
  have hrun := block_complete h (by simp [loadCode,addressCode,noFP])
  exact Option.some.inj (hrun.symm.trans (load_run s dst index offset valid))

theorem store_block_eq (h : Block (storeCode src index offset) s t)
    (h1 : src ≠ 1) (h2 : src ≠ 2)
    (valid : Valid64 s.globalStart s.globalBytes (address s index offset).toNat) :
    t = put (addressed s index offset) .global (address s index offset).toNat (s.regs src) := by
  have hrun := block_complete h (by simp [storeCode,addressCode,noFP])
  exact Option.some.inj (hrun.symm.trans (store_run s src index offset h1 h2 valid))

end PtxTorchLean.Poisson.PTX

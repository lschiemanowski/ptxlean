import PoissonPTX.SharedStore

/-! The active lane's six-instruction tree update. This scalar byte view is
not yet derived from the whole reduction's concurrent shared sources. -/
namespace PtxTorchLean.Poisson.PTX.Reduction.Update

/-- Register names match the emitted reduction: off=1, addr=2, shared=3,
a=4, b=5, acc=8 and lane=14. Offset is stride times eight bytes. -/
def code (offset : Word) : List Op :=
  [.wide8 1 (.reg 14), .add64 2 (.reg 3) (.reg 1),
   .load64 .shared 4 (.reg 2), .load64 .shared 5 (.offset 2 offset),
   .fp .add 8 (.reg 4) (.reg 5), .store64 .shared (.reg 2) (.reg 8)]

def address (s : State) : Word := s.regs 3 + wide s 14

def left (s : State) : Word := read64 s.shared (address s).toNat

def right (s : State) (offset : Word) : Word :=
  read64 s.shared (address s + offset).toNat

def loaded (s : State) (offset : Word) : State :=
  assign (assign (assign (assign s 1 (wide s 14)) 2 (address s))
    4 (left s)) 5 (right s offset)

def finish (s : State) (offset out : Word) : State :=
  put (assign (loaded s offset) 8 out) .shared (address s).toNat out

def Valid (s : State) (offset : Word) : Prop :=
  Valid64 s.sharedStart s.sharedBytes (address s).toNat ∧
  Valid64 s.sharedStart s.sharedBytes (address s + offset).toNat

/-- Inversion covers every permitted arithmetic result, not just a canonical
choice of NaN payload. Both load values and the stored word are derived. -/
theorem effect (h : Block (code offset) s t) :
    ∃ out, FP.Result .add (left s) (right s offset) out ∧
      t=finish s offset out := by
  cases h with | cons h1 rest =>
    cases h1
    cases rest with | cons h2 rest =>
      cases h2
      cases rest with | cons h3 rest =>
        cases h3
        cases rest with | cons h4 rest =>
          cases h4
          cases rest with | cons h5 rest =>
            cases h5 with | fp allowed =>
              rename_i out
              cases rest with | cons h6 rest =>
                cases h6
                cases rest
                refine ⟨out, ?_, ?_⟩
                · simpa [FP.Result,Operand.eval,address,left,right,wide,assign,advance,
                    State.memory] using allowed
                · simp [finish,loaded,address,left,right,wide,Operand.eval,assign,advance,
                    State.memory]

/-- The canonical executable witness uses exactly one rounded addition. -/
theorem run_update (valid : Valid s offset) :
    run (code offset) s = some (finish s offset
      (encode (decode (left s) + decode (right s offset)))) := by
  rcases valid with ⟨vl,vr⟩
  simp_all [code,run,eval,FP.apply,Operand.eval,State.start,State.bytes,State.memory,
    finish,loaded,address,left,right,wide,assign,advance]

theorem exists_execution (valid : Valid s offset) :
    ∃ t, Block (code offset) s t := ⟨_, run_sound (run_update valid)⟩

/-- The actual updated word decodes to the rounded pair sum, global memory is
unchanged, and only address/arithmetic scratch registers are changed. -/
theorem correct (h : Block (code offset) s t) :
    decode (read64 t.shared (address s).toNat) =
      decode (left s) + decode (right s offset) ∧
    t.global=s.global ∧
    (∀ r, r≠1 → r≠2 → r≠4 → r≠5 → r≠8 → t.regs r=s.regs r) := by
  obtain ⟨out,result,rfl⟩ := effect h
  refine ⟨?_, rfl, ?_⟩
  · simpa [finish,put,assign,advance,loaded,read64_write64,FP.Result,FP.apply]
      using result
  · intro r h1 h2 h4 h5 h8
    simp [finish,loaded,put,assign,advance,h1,h2,h4,h5,h8]

/-- A completed local update changes no bytes outside its own word. -/
theorem preserves_other_bytes (h : Block (code offset) s t)
    (outside : p < (address s).toNat ∨ (address s).toNat+8≤p) :
    t.shared p=s.shared p := by
  obtain ⟨out,_,rfl⟩ := effect h
  exact write64_outside s.shared (address s).toNat out p outside

theorem fetched_correct (pre suffix : List Op) (pc : s.pc=pre.length)
    (execution : Runs (pre++code offset++suffix) s t)
    (done : t.pc=pre.length+(code offset).length) :
    decode (read64 t.shared (address s).toNat) =
      decode (left s) + decode (right s offset) ∧ t.global=s.global := by
  have result := correct (Contraction.fetched_block _ _ _ execution pc done)
  exact ⟨result.1,result.2.1⟩

theorem fetched_exists (valid : Valid s offset) (pre suffix : List Op)
    (pc : s.pc=pre.length) :
    ∃ t, Runs (pre++code offset++suffix) s t ∧
      t.pc=pre.length+(code offset).length := by
  obtain ⟨t,ht⟩ := exists_execution valid
  exact ⟨t,block_fetched ht pre suffix pc,by rw [block_pc ht,pc]⟩

/-- Every active lane of each emitted stride has valid own/neighbor words.
The allocation and alignment conditions are concrete memory requirements. -/
theorem valid_of_active (s : State) (stride : Nat)
    (lane : (s.regs 14).toNat < stride) (hs : stride≤128)
    (base : (s.regs 3).toNat=s.sharedStart) (aligned : s.sharedStart%8=0)
    (fits : 2048≤s.sharedBytes) (noWrap : s.sharedStart+s.sharedBytes≤2^64) :
    Valid s (BitVec.ofNat 64 (stride*8)) := by
  have offBound : stride*8 < 2^64 := by omega
  have ownBound : (s.regs 3).toNat+(s.regs 14).toNat*8+0 < 2^64 := by
    rw [base]; omega
  have otherBound : (s.regs 3).toNat+(s.regs 14).toNat*8+
      (BitVec.ofNat 64 (stride*8)).toNat < 2^64 := by
    rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt offBound,base]; omega
  have own := SharedStore.location_exact s 0 (by omega) (by simpa using ownBound)
  have other := SharedStore.location_exact s (BitVec.ofNat 64 (stride*8)) (by omega) otherBound
  have ownExact : (address s).toNat = (s.regs 3).toNat+(s.regs 14).toNat*8 := by
    simpa [SharedStore.location,address] using own
  change (address s + BitVec.ofNat 64 (stride*8)).toNat = _ at other
  rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt offBound] at other
  unfold Valid
  rw [ownExact,other,base]
  constructor
  · exact ⟨by omega,by simp [Nat.add_mod,aligned],by omega,noWrap⟩
  · exact ⟨by omega,by simp [Nat.add_mod,aligned],by omega,noWrap⟩

end PtxTorchLean.Poisson.PTX.Reduction.Update

import PtxBinary32.GridDenseProgram

namespace Ptx.Scalar.Parallel.GridDense
open Ptx.Scalar.Parallel.Dense

theorem candidate_store_address (s : Dense.Shape) (b : Bounds s) (global : List Word)
    (seeds : Fin s.threads → Scalar.State) {events : List (Grid.Event s.rows s.width)} {final : Grid.State s.rows s.width}
    (run : Grid.Runs (config s b) (Dense.Compact.program s) (initial s global seeds) events final)
    (g : Fin s.rows) (t : Fin s.width) (space : Space) (occ : Scalar.Occurrence) (effect : MemoryEffect)
    (member : (g,.scalar t (some space) occ) ∈ events) (memory : occ.memory=some effect)
    (store : effect.kind=.store) :
    (occ.pc=20 ∧ space=.shared ∧ effect.address=bytePointer ((thread s g t).val%s.width)) ∨
    (∃ k, k<s.depth ∧ occ.pc=22+16*k+14 ∧ space=.shared ∧ effect.address=bytePointer (Dense.Compact.nextIndex s k (thread s g t))) ∨
    (occ.pc=22+16*s.depth+18 ∧ space=.global ∧ effect.address=bytePointer (outputIndex s (thread s g t)) ∧ (thread s g t).val%s.width=0) := by
  have conditions := Grid.run_memory_origin run g t space occ effect member memory
  obtain ⟨address,value,op,addr,gate⟩ := Grid.run_store run (fun g t => controlSeed s seeds (thread s g t)) (Dense.Compact.program_address_compatible s)
    (initial_aligned s global seeds) (initial_control s global seeds) g t (some space) occ effect member memory store
  have fetch := conditions.1
  rcases Dense.Compact.fetched_store_site s occ.pc space occ.instruction conditions.1 (by simpa [store] using conditions.2.2) with ⟨site,rfl⟩ | ⟨k,hk,site,rfl⟩ | ⟨site,rfl⟩
  · have instr : occ.instruction=Scalar.Instr.plain (.store (.reg 2) (.reg 6)) := by
      simpa [site,Dense.Compact.program,Dense.Compact.products,pointer,scalar,guarded] using fetch.symm
    have operands := Scalar.Op.store.inj (instr ▸ op).symm
    rw [operands.1] at addr
    exact .inl ⟨site,rfl,by simpa [Scalar.Operand64.eval,site,Dense.Compact.product_control_address s b.arithmetic seeds (thread s g t)] using addr⟩
  · rw [site,Dense.Compact.round_fetch s k hk 14 (by simp)] at fetch
    have instr : occ.instruction=⟨.pred 0 true,.store (.reg 2) (.reg 6)⟩ := by
      simpa [Dense.Compact.round,pointer,scalar,guarded] using fetch.symm
    have operands := Scalar.Op.store.inj (instr ▸ op).symm
    rw [operands.1] at addr
    exact .inr (.inl ⟨k,hk,site,rfl,by simpa [Scalar.Operand64.eval,site,Dense.Compact.round_control_address s b.arithmetic seeds (thread s g t) k hk] using addr⟩)
  · rw [site,Dense.Compact.output_fetch s 18 (by simp)] at fetch
    have instr : occ.instruction=⟨.pred 0 true,.store (.reg 6) (.reg 6)⟩ := by
      simpa [Dense.Compact.output,pointer,scalar,guarded] using fetch.symm
    have operands := Scalar.Op.store.inj (instr ▸ op).symm
    rw [operands.1] at addr
    have control := Dense.Compact.output_control_address s b.arithmetic seeds (thread s g t)
    have leader := gate (by rw [instr])
    rw [site,control.2] at leader
    exact .inr (.inr ⟨site,rfl,by simpa [Scalar.Operand64.eval,site,control.1] using addr,by simpa using leader⟩)


theorem candidate_load_address (s : Dense.Shape) (b : Bounds s) (global : List Word)
    (seeds : Fin s.threads → Scalar.State) {events : List (Grid.Event s.rows s.width)} {final : Grid.State s.rows s.width}
    (run : Grid.Runs (config s b) (Dense.Compact.program s) (initial s global seeds) events final)
    (g : Fin s.rows) (t : Fin s.width) (space : Space) (occ : Scalar.Occurrence) (effect : MemoryEffect)
    (member : (g,.scalar t (some space) occ) ∈ events) (memory : occ.memory=some effect) (load : effect.kind=.load) :
    (∃ weight : Bool, occ.pc=(if weight then 15 else 11) ∧ space=.global ∧ (thread s g t).val%s.width<s.columns ∧
      effect.address=bytePointer (if weight then s.weight ((thread s g t).val/s.width) ((thread s g t).val%s.width) else (thread s g t).val%s.width)) ∨
    (∃ k, k<s.depth ∧ ∃ right : Bool, occ.pc=22+16*k+(if right then 8 else 7) ∧ space=.shared ∧
      (thread s g t).val%s.width<2^(s.depth-(k+1)) ∧ effect.address=bytePointer (Dense.Compact.leftIndex s k (thread s g t)+if right then 1 else 0)) ∨
    (∃ bias : Bool, occ.pc=22+16*s.depth+(if bias then 10 else 5) ∧ space=(if bias then .global else .shared) ∧
      (thread s g t).val%s.width=0 ∧ effect.address=bytePointer (if bias then biasIndex s (thread s g t) else Dense.Compact.rootIndex s (thread s g t))) := by
  have conditions := Grid.run_memory_origin run g t space occ effect member memory
  obtain ⟨destination,address,op,addr,gate⟩ := Grid.run_load run (fun g t => controlSeed s seeds (thread s g t)) (Dense.Compact.program_address_compatible s)
    (initial_aligned s global seeds) (initial_control s global seeds) g t (some space) occ effect member memory load
  rcases Dense.Compact.fetched_load_site s occ.pc space occ.instruction conditions.1 (by simpa [load] using conditions.2.2) with
    ⟨weight,site,sp,inst⟩ | ⟨k,hk,right,site,sp,inst⟩ | ⟨bias,site,sp,inst⟩
  · have operands := Scalar.Op.load.inj (inst ▸ op).symm
    have control := Dense.Compact.product_read_control s b.arithmetic seeds (thread s g t) weight
    have enabled := gate (by rw [inst]; rfl)
    rw [site,control.2] at enabled
    rw [operands.2] at addr
    exact .inl ⟨weight,site,sp,by simpa using enabled,by simpa [Scalar.Operand64.eval,site,control.1] using addr⟩
  · have operands := Scalar.Op.load.inj (inst ▸ op).symm
    have control := Dense.Compact.round_read_control s b.arithmetic seeds (thread s g t) k hk right
    have enabled := gate (by rw [inst]; rfl)
    rw [site,control.2] at enabled
    rw [operands.2] at addr
    exact .inr (.inl ⟨k,hk,right,site,sp,by simpa using enabled,by simpa [Scalar.Operand64.eval,site,control.1] using addr⟩)
  · have operands := Scalar.Op.load.inj (inst ▸ op).symm
    have control := Dense.Compact.output_read_control s b.arithmetic seeds (thread s g t) bias
    have enabled := gate (by rw [inst]; rfl)
    rw [site,control.2] at enabled
    rw [operands.2] at addr
    exact .inr (.inr ⟨bias,site,sp,by simpa using enabled,by simpa [Scalar.Operand64.eval,site,control.1] using addr⟩)


end Ptx.Scalar.Parallel.GridDense

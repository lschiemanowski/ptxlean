import PoissonPTX.Tensor

namespace PtxTorchLean.Poisson.PTX.Kernel.Residual

/-- Connect the real register address calculation to the arena's binary64 array. -/
theorem setup_address : address (setup ctx s count).core 12 offset =
    address64 ctx.arena (index ctx) offset := by
  simp [address,wide,address64,BitVec.toNat_setWidth,Nat.mod_eq_of_lt (index ctx).isLt]

/-- Physical addresses, including the nonzero arena base, have not been replaced
by abstract array indices. A nonwrapping allocation and a field contained in it
suffice for every live cell's eight bytes to be valid. -/
theorem field_valid (ctx : Context) (s : State) (count : BitVec 32) (offset : Word)
    (hl : live ctx count)
    (start : s.core.globalStart = ctx.arena.toNat)
    (arenaAligned : ctx.arena.toNat % 8 = 0) (fieldAligned : offset.toNat % 8 = 0)
    (fieldBound : offset.toNat + count.toNat*8 ≤ s.core.globalBytes)
    (arenaBound : ctx.arena.toNat+s.core.globalBytes ≤ 2^64) :
    Valid64 s.core.globalStart s.core.globalBytes (address (setup ctx s count).core 12 offset).toNat := by
  have hidx : (index ctx).toNat < count.toNat := hl
  have bound : ctx.arena.toNat + (index ctx).toNat*8 + offset.toNat < 2^64 := by omega
  rw [setup_address,address64_exact _ _ _ bound]
  refine ⟨by omega,?_,by omega,by omega⟩
  omega

/-- Ordinary contiguous tensor arrays give the TorchLean result at the actual
launched index. Only input layout/allocation conditions and an execution are
premises; no value computed by the implementation is assumed. -/
theorem array_coordinate (ctx : Context) (s final : State) (count : BitVec 32)
    (rhs ap output : Word) (i : Fin count.toNat)
    (threadIndex : (index ctx).toNat = i.val)
    (pc : s.core.pc = 0) (running : s.halted = false)
    (start : s.core.globalStart = ctx.arena.toNat)
    (aligned : ctx.arena.toNat % 8 = 0)
    (arenaBound : ctx.arena.toNat+s.core.globalBytes ≤ 2^64)
    (fields : ∀ off ∈ [rhs,ap,output], off.toNat % 8 = 0 ∧
      off.toNat+count.toNat*8 ≤ s.core.globalBytes)
    (execution : Run ctx (program count rhs ap output) s final) :
    decode (read64 final.core.global (ctx.arena.toNat+i.val*8+output.toNat)) =
      (TorchLean.Tensor.subSpec
        (view s.core.global (fun j : Fin count.toNat => ctx.arena.toNat+j.val*8+rhs.toNat))
        (view s.core.global (fun j : Fin count.toNat => ctx.arena.toNat+j.val*8+ap.toNat))) (i,PUnit.unit) := by
  have hl : live ctx count := by unfold live; rw [threadIndex]; exact i.isLt
  have valid (off : Word) (h : off ∈ [rhs,ap,output]) :=
    field_valid ctx s count off hl start aligned (fields off h).1 (fields off h).2 arenaBound
  have addressExact (off : Word) (h : off ∈ [rhs,ap,output]) :
      (address (setup ctx s count).core 12 off).toNat = ctx.arena.toNat+i.val*8+off.toNat := by
    have hf := (fields off h).2
    have hi := i.isLt
    rw [setup_address,address64_exact _ _ _ (by rw [threadIndex]; omega),threadIndex]
  have hr := torchlean_coordinate ctx s final count rhs ap output i
    (fun j => ctx.arena.toNat+j.val*8+rhs.toNat)
    (fun j => ctx.arena.toNat+j.val*8+ap.toNat)
    (addressExact rhs (by simp)).symm (addressExact ap (by simp)).symm
    pc running hl (valid rhs (by simp)) (valid ap (by simp)) (valid output (by simp)) execution
  simpa only [addressExact output (by simp)] using hr

end PtxTorchLean.Poisson.PTX.Kernel.Residual

import PoissonPTX.ObservedParallelPadding

namespace PtxTorchLean.Poisson.PTX.Rounded

/-- Launch whole blocks of 256 lanes, including the final block's padding. -/
def count (nodes : Nat) : Nat := ((nodes+255)/256)*256

theorem enough : n≤count n := by unfold count; omega

theorem count_bound (small : n<2^30) : count n<2^32 := by unfold count; omega

def context (base : Word) (thread : Fin (count n)) : Kernel.Context :=
  ⟨base,BitVec.ofNat 32 (thread.val%256),BitVec.ofNat 32 (thread.val/256)⟩

theorem index (base : Word) (small : n<2^30) (thread : Fin (count n)) :
    (Kernel.Residual.index (context base thread)).toNat=thread.val := by
  have bound := count_bound small
  have inside := thread.isLt
  simp [Kernel.Residual.index,context,BitVec.toNat_add,BitVec.toNat_mul]
  omega

theorem live (base : Word) (small : n<2^30) (thread : Fin (count n)) :
    Kernel.Residual.live (context base thread) (BitVec.ofNat 32 n) ↔ thread.val<n := by
  unfold Kernel.Residual.live
  rw [index base small]
  have fits : n<2^32 := by omega
  simp only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt fits]

/-- Active coordinates preserve the same states while padding lanes execute
only their index setup and early return. -/
theorem run (base : Word) (small : n<2^30) {body : List Flow.Instr}
    {final : Fin n → Flow.State} (start : Fin (count n) → Flow.State)
    (pcs : ∀ t, (start t).core.pc=0) (running : ∀ t, (start t).halted=false)
    (actual : Flow.Parallel.Runs (fun t : Fin n => context base (t.castLE enough))
      (VectorFlowEntry.program (BitVec.ofNat 32 n) body)
      (fun t => start (t.castLE enough)) words indices final)
    (done : ∀ t, (final t).halted=true) :
    ∃ result, Flow.Parallel.Runs (context base) (VectorFlowEntry.program (BitVec.ofNat 32 n) body) start
      (words.map (Flow.Parallel.renameEvent (Fin.castLE enough)))
      (indices.map (fun (owner,access) => (owner.castLE enough,access))) result ∧
      (∀ t, (result t).halted=true) ∧ (∀ t, result (t.castLE enough)=final t) := by
  have sameStart : Flow.Parallel.extend enough (fun t : Fin n => start (t.castLE enough)) start=start := by
    funext t
    simp only [Flow.Parallel.extend]
    split <;> rfl
  obtain ⟨extended,halted⟩ := Flow.Parallel.complete_padding enough start (fun _ => rfl)
    actual done (fun t _ => pcs t) (fun t _ => running t)
    (by intro t inactive; rw [live base small]; omega)
  rw [sameStart] at extended
  exact ⟨_,extended,halted,fun t => Flow.Parallel.extend_active _ _ _ t⟩

end PtxTorchLean.Poisson.PTX.Rounded

import PtxBinary32.GridDenseAddress
import PtxBinary32.DenseOwnership
import PtxBinary32.GridControl
import PtxBinary32.GridGraphOrigins

/-! Address ownership for the actual combined grid trace. Global input slices
are read-only across all groups; scratch identities include the group. -/
namespace Ptx.Scalar.Parallel.GridDense
open Ptx.Scalar.Parallel.Dense

theorem candidate_shared_owner (s : Dense.Shape) (b : Bounds s) (global : List Word)
    (seeds : Fin s.threads → Scalar.State) {events : List (Grid.Event s.rows s.width)} {final : Grid.State s.rows s.width}
    (run : Grid.Runs (config s b) (program s) (initial s global seeds) events final)
    (g : Fin s.rows) (t : Fin s.width) (occ : Scalar.Occurrence) (effect : MemoryEffect)
    (member : (g,.scalar t (some .shared) occ) ∈ events) (memory : occ.memory=some effect)
    (store : effect.kind=.store) :
    ∃ phase, phase≤s.depth ∧ occ.pc=sharedStorePC phase ∧ effect.address=bytePointer (phase*s.threads+(thread s g t).val) := by
  rcases candidate_store_address s b global seeds run g t .shared occ effect member memory store with h | h | h
  · exact ⟨0,Nat.zero_le _,by simpa [sharedStorePC] using h.1,by simpa using h.2.2⟩
  · obtain ⟨k,hk,pc,_,addr⟩ := h
    exact ⟨k+1,hk,by simpa [sharedStorePC] using pc,by simpa [nextIndex,Nat.add_comm] using addr⟩
  · cases h.2.1

theorem candidate_global_owner (s : Dense.Shape) (b : Bounds s) (global : List Word)
    (seeds : Fin s.threads → Scalar.State) {events : List (Grid.Event s.rows s.width)} {final : Grid.State s.rows s.width}
    (run : Grid.Runs (config s b) (program s) (initial s global seeds) events final)
    (g : Fin s.rows) (t : Fin s.width) (occ : Scalar.Occurrence) (effect : MemoryEffect)
    (member : (g,.scalar t (some .global) occ) ∈ events) (memory : occ.memory=some effect)
    (store : effect.kind=.store) :
    occ.pc=22+16*s.depth+18 ∧ effect.address=bytePointer (outputIndex s (thread s g t)) ∧ (thread s g t).val%s.width=0 := by
  rcases candidate_store_address s b global seeds run g t .global occ effect member memory store with h | h | h
  · cases h.2.1
  · obtain ⟨_,_,_,h,_⟩ := h; cases h
  · exact ⟨h.1,h.2.2⟩



private theorem pointer_word (g : Fin groups) (i : Nat) (fit : i<2^32) (space : Space) :
    (Grid.location g space (bytePointer i)).word=i := by
  have bound : 4*i<18446744073709551616 := by omega
  simp [Grid.location,bytePointer,BitVec.toNat_ofNat,Nat.mod_eq_of_lt bound]

private theorem same_pointer_index (g h : Fin groups) (i j : Nat) (hi : i<2^32) (hj : j<2^32) (space : Space)
    (same : (Grid.location g space (bytePointer i)).code=(Grid.location h space (bytePointer j)).code) : i=j := by
  have eq := congrArg Ptx.TraceMemory.Location.word (Ptx.TraceMemory.Location.code_injective same)
  simpa [pointer_word g i hi space,pointer_word h j hj space] using eq

private theorem scratch_index_fits (s : Dense.Shape) (b : Bounds s) (t : Fin s.threads) (p : Nat) (hp : p≤s.depth) :
    p*s.threads+t.val<2^32 := by
  have ht := t.isLt
  have mul := Nat.mul_le_mul_right s.threads hp
  have bound := b.arithmetic.arithmetic
  dsimp [Shape.sharedWords] at bound
  rw [Nat.add_mul] at bound
  omega

theorem scalar_site_unique (s : Dense.Shape) {cfg : Grid.Config s.width} {start final : Grid.State s.rows s.width}
    {events : List (Grid.Event s.rows s.width)} (run : Grid.Runs cfg (program s) start events final)
    (p q : Nat) (g : Fin s.rows) (t : Fin s.width) (space otherSpace : Option Space)
    (e f : Scalar.Occurrence)
    (hp : events[p]?=some (g,.scalar t space e)) (hq : events[q]?=some (g,.scalar t otherSpace f))
    (same : e.pc=f.pc) : p=q :=
  Grid.Control.same_site_unique run (program_straight s) p q _ _ (g,t) e.pc hp hq rfl (by simp [Grid.Control.stamp,Control.stamp,same])

/-- Location identity includes the CTA, and a private plane/word identifies its
sole issuing instruction. Repeating that site is ruled out by the actual trace. -/
theorem shared_store_unique (s : Dense.Shape) (b : Bounds s) (global : List Word)
    (seeds : Fin s.threads → Scalar.State) {events : List (Grid.Event s.rows s.width)} {final : Grid.State s.rows s.width}
    (run : Grid.Runs (config s b) (program s) (initial s global seeds) events final)
    (p q : Nat) (g h : Fin s.rows) (t u : Fin s.width) (e f : Scalar.Occurrence) (a z : MemoryEffect)
    (hp : events[p]?=some (g,.scalar t (some .shared) e)) (hq : events[q]?=some (h,.scalar u (some .shared) f))
    (he : e.memory=some a) (hf : f.memory=some z) (ha : a.kind=.store) (hz : z.kind=.store)
    (same : (Grid.location g .shared a.address).code=(Grid.location h .shared z.address).code) : p=q := by
  have gh : g=h := by
    by_contra different
    exact Grid.shared_private g h a.address z.address different same
  subst h
  obtain ⟨i,hi,pc,addr⟩ := candidate_shared_owner s b global seeds run g t e a (List.mem_of_getElem? hp) he ha
  obtain ⟨j,hj,qc,bddr⟩ := candidate_shared_owner s b global seeds run g u f z (List.mem_of_getElem? hq) hf hz
  rw [addr,bddr] at same
  have indices := same_pointer_index g g _ _ (scratch_index_fits s b (thread s g t) i hi) (scratch_index_fits s b (thread s g u) j hj) .shared same
  have tn := (thread s g t).isLt
  have un := (thread s g u).isLt
  have pos : 0<s.threads := by omega
  have owner := congrArg (· % s.threads) indices
  simp [Nat.add_mod,Nat.mod_eq_of_lt tn,Nat.mod_eq_of_lt un] at owner
  have tid := (thread_unique s g g t u (Fin.ext owner)).2
  subst u
  have phase : i=j := Nat.mul_right_cancel pos (by omega)
  exact scalar_site_unique s run p q g t _ _ e f hp hq (by rw [pc,qc,phase])

/-- Equal global output addresses identify the row group and its column-zero
writer. Foreign groups cannot write that output, regardless of schedule. -/
theorem global_store_unique (s : Dense.Shape) (b : Bounds s) (global : List Word)
    (seeds : Fin s.threads → Scalar.State) {events : List (Grid.Event s.rows s.width)} {final : Grid.State s.rows s.width}
    (run : Grid.Runs (config s b) (program s) (initial s global seeds) events final)
    (p q : Nat) (g h : Fin s.rows) (t u : Fin s.width) (e f : Scalar.Occurrence) (a z : MemoryEffect)
    (hp : events[p]?=some (g,.scalar t (some .global) e)) (hq : events[q]?=some (h,.scalar u (some .global) f))
    (he : e.memory=some a) (hf : f.memory=some z) (ha : a.kind=.store) (hz : z.kind=.store)
    (same : (Grid.location g .global a.address).code=(Grid.location h .global z.address).code) : p=q := by
  obtain ⟨pc,addr,leader⟩ := candidate_global_owner s b global seeds run g t e a (List.mem_of_getElem? hp) he ha
  obtain ⟨qc,bddr,other⟩ := candidate_global_owner s b global seeds run h u f z (List.mem_of_getElem? hq) hf hz
  rw [addr,bddr] at same
  have fits (v : Fin s.threads) : outputIndex s v<2^32 := by
    have := (output_indices s v).2.2; have := b.arithmetic.arithmetic; omega
  have indices := same_pointer_index g h _ _ (fits (thread s g t)) (fits (thread s h u)) .global same
  have row : g=h := by
    apply Fin.ext
    simpa [outputIndex,(thread_coordinates s g t).1,(thread_coordinates s h u).1] using indices
  have lane : t=u := by
    apply Fin.ext
    rw [(thread_coordinates s g t).2] at leader
    rw [(thread_coordinates s h u).2] at other
    omega
  subst h; subst u
  exact scalar_site_unique s run p q g t _ _ e f hp hq (by omega)

end Ptx.Scalar.Parallel.GridDense

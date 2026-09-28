import PoissonPTX.SharedStore
import PoissonPTX.Sources
import PoissonPTX.ContractionLayout

/-! Order-independent publication of disjoint binary64 words. This constructs
storage from actual instruction results, not a barrier admission theorem. -/
namespace PtxTorchLean.Poisson.PTX.SharedPlane

def address (base width plane lane : Nat) : Nat := base+(plane*width*width+lane)*8

/-- Generated plane and lane operands imply the physical publication address. -/
theorem store_address (s : State) (base width : Nat) (plane : Fin 7)
    (i : Fin (width*width)) (hw : width≤5)
    (hb : (s.regs 3).toNat=base) (hi : (s.regs 14).toNat=i.val)
    (fits : base+7*width*width*8≤2^64) :
    (SharedStore.location s (BitVec.ofNat 64 (plane.val*width*width*8))).toNat =
      address base width plane.val i.val := by
  have hp := plane.isLt
  have hil := i.isLt
  have hsmall : width*width≤25 := by nlinarith
  have po : plane.val*width*width*8<2^64 := by nlinarith
  have endBound : i.val*8+plane.val*width*width*8+8≤7*width*width*8 := by
    have h := Nat.mul_le_mul_right (width*width) (show plane.val+1≤7 by omega)
    nlinarith
  have bound : (s.regs 3).toNat+(s.regs 14).toNat*8+
      (BitVec.ofNat 64 (plane.val*width*width*8)).toNat<2^64 := by
    rw [hb,hi,BitVec.toNat_ofNat,Nat.mod_eq_of_lt po]; omega
  rw [SharedStore.location_exact s _ (by rw [hi]; omega) bound,
    BitVec.toNat_ofNat,Nat.mod_eq_of_lt po,hb,hi]
  simp [address]; ring

theorem owners (base width plane : Nat) (i j : Fin (width*width)) (hne : i≠j) :
    Sources.Disjoint (address base width plane i.val) (address base width plane j.val) := by
  have h : i.val≠j.val := fun e => hne (Fin.ext e)
  unfold Sources.Disjoint address
  omega

theorem planes_disjoint (base width : Nat) (p q : Nat) (hne : p≠q)
    (i j : Fin (width*width)) :
    Sources.Disjoint (address base width p i.val) (address base width q j.val) := by
  have hi := i.isLt; have hj := j.isLt
  have hpq : p<q ∨ q<p := by omega
  unfold Sources.Disjoint address
  rcases hpq with h | h
  · left
    have hh := Nat.mul_le_mul_right (width*width) (show p+1≤q by omega)
    nlinarith
  · right
    have hh := Nat.mul_le_mul_right (width*width) (show q+1≤p by omega)
    nlinarith

/-- The source word is read from each lane's actual post-store memory. -/
def publish (initial : Memory) (base width plane : Nat)
    (final : Fin (width*width) → State) : List (Fin (width*width)) → Memory
  | [] => initial
  | i::rest => write64 (publish initial base width plane final rest)
      (address base width plane i.val) (read64 (final i).shared (address base width plane i.val))

theorem published_word (initial : Memory) (base width plane : Nat)
    (final : Fin (width*width) → State) (order : List (Fin (width*width)))
    (i : Fin (width*width)) (included : i∈order) :
    read64 (publish initial base width plane final order) (address base width plane i.val) =
      read64 (final i).shared (address base width plane i.val) := by
  induction order with
  | nil => simp at included
  | cons j rest ih =>
    by_cases same : j=i
    · subst j; simp [publish]
    · rw [publish,read64_write64_disjoint _ _ _ _ (owners base width plane j i same)]
      exact ih ((List.mem_cons.mp included).resolve_left (Ne.symm same))

theorem published_outside (initial : Memory) (base width plane : Nat)
    (final : Fin (width*width) → State) (order : List (Fin (width*width))) (p : Nat)
    (outside : ∀ i : Fin (width*width), p<address base width plane i.val ∨
      address base width plane i.val+8≤p) :
    publish initial base width plane final order p = initial p := by
  induction order with
  | nil => rfl
  | cons i rest ih => rw [publish,write64_outside _ _ _ _ (outside i),ih]

/-- A complete publication has a unique whole-memory result, including gaps.
Duplicates are harmless because each lane has one fixed completed store. -/
theorem order_independent (initial : Memory) (base width plane : Nat)
    (final : Fin (width*width) → State) (left right : List (Fin (width*width)))
    (hl : ∀ i, i∈left) (hr : ∀ i, i∈right) :
    publish initial base width plane final left = publish initial base width plane final right := by
  funext p
  by_cases covered : ∃ i : Fin (width*width), ∃ k : Fin 8, p=address base width plane i.val+k.val
  · obtain ⟨i,k,rfl⟩ := covered
    have l := congrArg (fun w => byte w k.val) (published_word initial base width plane final left i (hl i))
    have r := congrArg (fun w => byte w k.val) (published_word initial base width plane final right i (hr i))
    simpa only [Sources.byte_read64] using l.trans r.symm
  · have outside : ∀ i : Fin (width*width), p<address base width plane i.val ∨
        address base width plane i.val+8≤p := by
      intro i
      by_contra h
      have hk : p-address base width plane i.val<8 := by omega
      exact covered ⟨i,⟨p-address base width plane i.val,hk⟩,by simp; omega⟩
    rw [published_outside _ _ _ _ _ _ _ outside,published_outside _ _ _ _ _ _ _ outside]

/-- The published word is the source register of an actually executed store. -/
theorem published_store (initial : Memory) (base width plane src : Nat) (offset : Word)
    (start final : Fin (width*width) → State) (order : List (Fin (width*width)))
    (h1 : src≠1) (h2 : src≠2)
    (valid : ∀ i, SharedStore.Valid (start i) offset)
    (locations : ∀ i, (SharedStore.location (start i) offset).toNat=address base width plane i.val)
    (execution : ∀ i, Block (SharedStore.code offset src) (start i) (final i))
    (i : Fin (width*width)) (included : i∈order) :
    read64 (publish initial base width plane final order) (address base width plane i.val) =
      (start i).regs src := by
  rw [published_word _ _ _ _ _ _ i included,
    SharedStore.block_eq (execution i) h1 h2 (valid i)]
  simp [SharedStore.finish,put,advance,assign,locations i]

/-- All coordinates follow from the actual contraction/store executions. No
premise asserts that a producer phase already has the correct matrix answer. -/
theorem published_contraction (initial : Memory) (base width plane acc : Nat) (offset : Word)
    (a b : Contraction.Matrix) (start final : Fin (width*width) → State)
    (order : List (Fin (width*width))) (complete : ∀ i, i∈order)
    (allowed : Contraction.Accumulator acc)
    (loads : ∀ i k, k<width → Contraction.Valid (start i) width k a ∧ Contraction.Valid (start i) width k b)
    (valid : ∀ i, SharedStore.Valid (start i) offset)
    (locations : ∀ i, (SharedStore.location (start i) offset).toNat=address base width plane i.val)
    (execution : ∀ i, Block (Contraction.program width acc a b ++ SharedStore.code offset acc)
      (start i) (final i)) (i : Fin (width*width)) :
    decode (read64 (publish initial base width plane final order) (address base width plane i.val)) =
      Spec.get2 (Spec.matMulSpec (Contraction.leftTensor (start i) width a)
        (Contraction.rightTensor (start i) width b)) 0 0 := by
  rw [published_word _ _ _ _ _ _ i (complete i)]
  have h := (SharedStore.contraction_store allowed (loads i) (valid i) (execution i)).1
  simpa only [locations i] using h

/-- Reading a row-major matrix operand from the published plane recovers the
word of the lane owning that coordinate. This is a snapshot lemma, not a
claim that an arbitrary concurrent load has already observed publication. -/
theorem contraction_value (initial : Memory) (base width plane : Nat)
    (final : Fin (width*width) → State) (order : List (Fin (width*width)))
    (complete : ∀ i, i∈order) (s : State) (k : Nat) (m : Contraction.Matrix)
    (sp : m.space=.shared) (hw : width≤5)
    (hr : ((m.row.operand k).eval s).toNat<width)
    (hc : ((m.column.operand k).eval s).toNat<width)
    (baseEq : (s.regs 3).toNat=base) (off : m.offset.toNat=plane*width*width*8)
    (bound : base+plane*width*width*8+width*width*8≤2^64)
    (memory : s.shared=publish initial base width plane final order) :
    ∃ i : Fin (width*width),
      i.val=((m.row.operand k).eval s).toNat*width+((m.column.operand k).eval s).toNat ∧
      Contraction.value s width k m = decode (read64 (final i).shared (address base width plane i.val)) := by
  have indexBound : ((m.row.operand k).eval s).toNat*width+
      ((m.column.operand k).eval s).toNat<width*width := by
    nlinarith
  let i : Fin (width*width) := ⟨_,indexBound⟩
  refine ⟨i,rfl,?_⟩
  have hb : (s.regs (Contraction.baseRegister m.space)).toNat+
      (((m.row.operand k).eval s).toNat*width+((m.column.operand k).eval s).toNat)*8+
      m.offset.toNat<2^64 := by
    simp only [sp,Contraction.baseRegister,baseEq,off]; omega
  unfold Contraction.value
  rw [Contraction.location_exact s width k m hw hr hc hb]
  simp only [sp,State.memory,Contraction.baseRegister,baseEq,off,memory]
  have addr : base+(((m.row.operand k).eval s).toNat*width+
      ((m.column.operand k).eval s).toNat)*8+plane*width*width*8=address base width plane i.val := by
    simp [address,i]; ring
  rw [addr,published_word _ _ _ _ _ _ i (complete i)]

end PtxTorchLean.Poisson.PTX.SharedPlane

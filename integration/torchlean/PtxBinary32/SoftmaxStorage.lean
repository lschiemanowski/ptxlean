import PtxBinary32.SoftmaxSweep

/-! Arena equalities for softmax composition. These are proofs about actual
stored words, not host operations that manufacture intermediate arithmetic. -/
namespace Ptx.Scalar.SoftmaxStorage
open Parallel

def row (n : Nat) (memory : List Word) : Fin n → Word := fun i => memory[i.val]!

theorem bang_eq {a b : List Word} {i j : Nat} (eq : a[i]?=b[j]?) : a[i]! = b[j]! := by
  simpa only [List.getElem!_eq_getElem?_getD] using congrArg (fun x => x.getD (default:Word)) eq

theorem some_bang (memory : List Word) (i : Nat) (inside : i<memory.length) :
    memory[i]?=some memory[i]! := by simp [inside]

theorem global_tail (d : Nat) (a b : Fin (Sum.width d) → Word)
    (i : Nat) (outside : Sum.width d ≤ i) : (Sum.global d a)[i]?=(Sum.global d b)[i]? := by
  simp [Sum.global,List.getElem?_append,Nat.not_lt.mpr outside]

theorem global_eq (d : Nat) (input : Fin (Sum.width d) → Word) (memory : List Word)
    (len : memory.length=2*Sum.width d+2)
    (tail : ∀ i, Sum.width d ≤ i → memory[i]?=(Sum.global d input)[i]?) :
    memory=Sum.global d (row (Sum.width d) memory) := by
  apply List.ext_getElem?
  intro i
  by_cases hi : i<Sum.width d
  · rw [Sum.global_input d _ ⟨i,hi⟩]
    exact some_bang memory i (by omega)
  · exact (tail i (by omega)).trans (global_tail d _ _ i (by omega))

/-- Restore the weight temporarily occupied by the maximum. The row words
are already outputs of the in-place exponential pass. -/
theorem restore_weight (d : Nat) (input : Fin (Sum.width d) → Word) (maximum : Word)
    (memory : List Word) (len : memory.length=2*Sum.width d+2)
    (tail : ∀ i, Sum.width d ≤ i →
      memory[i]?=((Sum.global d input).set (Sum.width d) maximum)[i]?) :
    memory.set (Sum.width d) 0x3f800000 = Sum.global d (row (Sum.width d) memory) := by
  have rowEq : row (Sum.width d) (memory.set (Sum.width d) 0x3f800000)=row (Sum.width d) memory := by
    funext i
    apply bang_eq
    exact List.getElem?_set_ne (by have := i.isLt; omega)
  rw [← rowEq]
  apply global_eq d input
  · simpa using len
  · intro i hi
    by_cases eq : i=Sum.width d
    · subst i
      rw [List.getElem?_set_self (by omega)]
      have value := Sum.global_weight d input 0 (by simp [Sum.width])
      simp only [Nat.add_zero] at value
      rw [some_bang _ _ (by simp; omega),value]
    · rw [List.getElem?_set_ne (by omega),tail i hi,List.getElem?_set_ne (by omega)]

/-- A pass obtains both operands by its actual stage contract. The shared
second operand lies beyond the overwritten prefix. -/
theorem pass_relations {stage : Nat → List Word → List Word → Prop}
    {relation : Word → Word → Word → Prop} {count denominator : Nat}
    {before after : List Word}
    (contract : ∀ i a b, stage i a b → ∃ out,
      relation a[i]! a[denominator]! out ∧ b=a.set i out)
    (run : SoftmaxSweep.Run stage count before after)
    (allocated : count ≤ before.length) (separate : count ≤ denominator) :
    ∀ i : Fin count, relation before[i.val]! before[denominator]! after[i.val]! := by
  have writes : SoftmaxSweep.WritesOwn stage := by
    intro i a b h
    obtain ⟨out,_,eq⟩ := contract i a b h
    exact ⟨out,eq⟩
  intro i
  obtain ⟨a,b,op,len,input,tail,result⟩ := SoftmaxSweep.occurrence writes run i.val i.isLt
  obtain ⟨out,rel,eq⟩ := contract i.val a b op
  have finalWord : after[i.val]! = out := by
    have inside : i.val<a.length := by rw [len]; have := i.isLt; omega
    have stored : b[i.val]?=some out := by rw [eq,List.getElem?_set_self inside]
    have finalStored := result.symm.trans stored
    simp [List.getElem!_eq_getElem?_getD,finalStored]
  rw [bang_eq input,bang_eq (tail denominator separate)] at rel
  simpa only [finalWord] using rel

end Ptx.Scalar.SoftmaxStorage

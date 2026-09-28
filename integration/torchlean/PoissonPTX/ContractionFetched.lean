import PoissonPTX.Contraction
import PoissonQuadCorrespondence

namespace PtxTorchLean.Poisson.PTX.Contraction

/-- Straight-line instruction steps increase the fetched program counter. -/
theorem runs_pc_le (h : Runs code s t) : s.pc ≤ t.pc := by
  induction h with
  | nil => exact Nat.le_refl _
  | cons step rest ih =>
    obtain ⟨op,fetch,ev⟩ := step
    have hp := eval_pc ev
    omega

theorem runs_eq_of_pc (h : Runs code s t) (pc : s.pc=t.pc) : s=t := by
  cases h with
  | nil => rfl
  | cons step rest =>
    obtain ⟨op,fetch,ev⟩ := step
    have hp := eval_pc ev
    have ht := runs_pc_le rest
    omega

/-- A completed fetched block cannot skip instructions or execute a supplied
scalar stream instead. Prefix and suffix are arbitrary surrounding code. -/
theorem fetched_block (pre code suffix : List Op) (h : Runs (pre++code++suffix) s t)
    (pc : s.pc=pre.length) (done : t.pc=pre.length+code.length) : Block code s t := by
  induction code generalizing pre s with
  | nil =>
    have eq := runs_eq_of_pc h (by simpa using pc.trans done.symm)
    subst t
    exact .nil
  | cons op ops ih =>
    cases h with
    | nil => simp only [List.length_cons] at done; omega
    | cons step rest =>
      obtain ⟨actual,fetch,ev⟩ := step
      have same : op=actual := by simpa [pc] using fetch
      subst actual
      apply Block.cons ev
      apply ih (pre++[op]) (by simpa [List.append_assoc] using rest)
      · simp [eval_pc ev,pc]
      · simp only [List.length_append,List.length_singleton,List.length_cons,List.length_nil] at done ⊢
        omega

/-- The tensor operands are views of the actual bytes selected by the instruction
address calculation. No precomputed matrix-product answer is supplied. -/
def leftTensor (s : State) (width : Nat) (a : Matrix) : Mat Float 1 width :=
  matrix fun _ k => value s width k.val a

def rightTensor (s : State) (width : Nat) (b : Matrix) : Mat Float width 1 :=
  matrix fun k _ => value s width k.val b

theorem tensor_fold (s : State) (width : Nat) (a b : Matrix) :
    Spec.get2 (Spec.matMulSpec (leftTensor s width a) (rightTensor s width b)) 0 0 =
      (List.range width).foldl (fun z k => z + value s width k a * value s width k b) 0 := by
  simp [leftTensor,rightTensor,matrix,Spec.get2,Spec.get,
    TorchLean.Tensor.getScalar,TorchLean.Tensor.unstack,TorchLean.Tensor.item,
    Spec.matMulSpec]
  have indices : (List.finRange width).map Fin.val = List.range width := by
    apply List.ext_getElem
    · simp
    · intro i hi hj; simp
  rw [← indices,List.foldl_map]

/-- All completed fetched contraction blocks equal the pinned TorchLean matrix
product on byte views, preserving the input memories and live index registers. -/
theorem fetched_correct (allowed : Accumulator acc)
    (valid : ∀ k<width, Valid s width k a ∧ Valid s width k b)
    (pre suffix : List Op) (pc : s.pc=pre.length)
    (execution : Runs (pre++program width acc a b++suffix) s t)
    (done : t.pc=pre.length+(program width acc a b).length) :
    decode (t.regs acc) =
      Spec.get2 (Spec.matMulSpec (leftTensor s width a) (rightTensor s width b)) 0 0 ∧
    Stable s t := by
  rw [tensor_fold]
  exact correct allowed valid (fetched_block _ _ _ execution pc done)

theorem fetched_exists (s : State) (allowed : Accumulator acc)
    (valid : ∀ k<width, Valid s width k a ∧ Valid s width k b)
    (pre suffix : List Op) (pc : s.pc=pre.length) :
    ∃ t, Runs (pre++program width acc a b++suffix) s t ∧
      t.pc=pre.length+(program width acc a b).length := by
  obtain ⟨t,ht⟩ := exists_execution s allowed valid
  exact ⟨t,block_fetched ht pre suffix pc,by rw [block_pc ht,pc]⟩

end PtxTorchLean.Poisson.PTX.Contraction

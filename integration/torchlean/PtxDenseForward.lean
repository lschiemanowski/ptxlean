import PtxDenseVJP
import PtxBinary32.DenseAdmission
import PtxBinary32.ReductionPadding

/-! Actual admitted dense-forward output words compared to the actual TorchLean
real tensor graph. Entry encodings and range checks are explicit; the tensor/tree
identity is proved, not a premise. This concerns a selected execution. -/
namespace PtxTorchLean.DenseForward
open Ptx Ptx.Binary32 Ptx.Scalar.Parallel
open TorchLean TorchLean.Tensor

/-- Initial encoded operands and their corresponding ideal tensor entries.
Range guards concern the explicit rounded tree, not unknown execution values. -/
structure Encoding (s : Dense.Shape) (global : List Word)
    (x : Tensor ℝ (DenseVJP.column s.columns))
    (w : Tensor ℝ (DenseVJP.matrix s.rows s.columns))
    (b : Tensor ℝ (DenseVJP.column s.rows)) where
  entry : Fin s.rows → Fin s.columns → DotError.Input
  weightWord : ∀ r c, (entry r c).left = global[s.weight r.val c.val]!
  inputWord : ∀ r c, (entry r c).right = global[c.val]!
  weightIdeal : ∀ r c, (entry r c).l = Spec.get2 w r c
  inputIdeal : ∀ r c, (entry r c).r = Spec.get2 x c 0
  biasValue : Fin s.rows → ℝ
  biasError : Fin s.rows → ℝ
  biasReal : ∀ r, finiteReal global[s.biasBase+r.val]! = some (biasValue r)
  biasApprox : ∀ r, |biasValue r-Spec.get2 b r 0| ≤ biasError r
  treeSafe : ∀ r, Reduction.Safe (Reduction.balanced s.depth 0 (Reduction.paddedInput (entry r)))
  additionRange : ∀ r, |Reduction.rounded (Reduction.balanced s.depth 0 (Reduction.paddedInput (entry r)))+
    biasValue r| ≤ Bounds.maxFinite

noncomputable def Encoding.row (encoding : Encoding s global x w b) (r : Fin s.rows) : Reduction.RowInput where
  tree := Reduction.balanced s.depth 0 (Reduction.paddedInput (encoding.entry r))
  safe := encoding.treeSafe r
  bias := global[s.biasBase+r.val]!
  bh := encoding.biasValue r
  b := Spec.get2 b r 0
  eb := encoding.biasError r
  biasReal := encoding.biasReal r
  biasError := encoding.biasApprox r
  additionRange := encoding.additionRange r

/-- Padded encoded leaves match the operands actually used by the kernel. -/
theorem Encoding.row_words (encoding : Encoding s global x w b) (r : Fin s.rows) :
    Reduction.words (encoding.row r).tree = Reduction.balanced s.depth 0 (Dense.operands s global r.val) := by
  unfold Encoding.row Reduction.words
  rw [Reduction.map_balanced]
  apply congrArg (Reduction.balanced s.depth 0)
  funext c
  by_cases h : c<s.columns
  · simp [Reduction.paddedInput,h,Dense.operands,encoding.weightWord,encoding.inputWord]
  · simp [Reduction.paddedInput,h,Dense.operands,Reduction.zeroInput]

/-- Zero padding and real associativity identify the actual TorchLean affine
coordinate. This includes the empty input dimension. -/
theorem Encoding.row_ideal (encoding : Encoding s global x w b) (r : Fin s.rows) :
    (encoding.row r).idealAffine = Spec.get2 (DenseVJP.affine x w b) r 0 := by
  rw [DenseVJP.affine_coordinate]
  unfold Reduction.RowInput.idealAffine Encoding.row
  rw [Reduction.padded_ideal _ _ s.padded]
  simp [encoding.weightIdeal,encoding.inputIdeal]

/-- Stored reference words have finite real values with an error measured
against the upstream tensor graph, rather than an independently stated sum. -/
theorem forward_word_accuracy (encoding : Encoding s global x w b) (r : Fin s.rows) :
    finiteReal (Dense.forwardWord s global r.val) = some (max (encoding.row r).affine 0) ∧
      |max (encoding.row r).affine 0 -
        Spec.get2 ((DenseVJP.graph s.rows s.columns).forward (DenseVJP.inputs x w b)) r 0| ≤ (encoding.row r).error := by
  have accuracy := Dense.forward_accuracy s global r.val (encoding.row r) (encoding.row_words r) rfl
  refine ⟨accuracy.1,?_⟩
  rw [encoding.row_ideal] at accuracy
  simpa [DenseVJP.forward_coordinate,DenseVJP.affine_coordinate] using accuracy.2

/-- The actual upstream TorchLean output bounds the real interpretation of
words stored by one complete admitted kernel execution. No graph-value or
intermediate-accuracy identity is a caller premise. -/
theorem selected_forward (s : Dense.Shape) (bounds : Dense.Bounds s) (global shared : List Word)
    (seeds : Fin s.threads → Ptx.Scalar.State)
    (x : Tensor ℝ (DenseVJP.column s.columns))
    (w : Tensor ℝ (DenseVJP.matrix s.rows s.columns))
    (b : Tensor ℝ (DenseVJP.column s.rows)) (encoding : Encoding s global x w b)
    (globalBound : s.globalWords ≤ global.length) (sharedBound : s.sharedWords ≤ shared.length) :
    ∃ events final, ∃ run : ConcreteRuns (Dense.config s bounds) (Dense.program s)
      (Dense.initial s global shared seeds) events final, ∃ source co,
      Graph.Ordered.Valid (Memory.graph (Dense.program s) global shared events source co)
        (Memory.runOrder run.toRuns
          (show (Dense.initial s global shared seeds).barrier = Barrier.reset 0 from rfl) source co).cross ∧
      (∀ i, ¬Path (Ptx.Scalar.SharedReduction.Machine.Memory.grounding
        (Memory.graph (Dense.program s) global shared events source co)
        (Memory.runOrder run.toRuns
          (show (Dense.initial s global shared seeds).barrier = Barrier.reset 0 from rfl) source co).cross) i i) ∧
      (∀ t, (final.lanes t).halted = true ∧ (final.lanes t).scalar.pc = (Dense.program s).length-1) ∧
      (∀ row : Fin s.rows, ∃ word, final.global[s.outputBase+row.val]? = some word ∧
        finiteReal word = some (max (encoding.row row).affine 0) ∧
        |max (encoding.row row).affine 0 -
          Spec.get2 ((DenseVJP.graph s.rows s.columns).forward (DenseVJP.inputs x w b)) row 0| ≤
          (encoding.row row).error) ∧
      (∀ i, i<s.outputBase → final.global[i]? = global[i]?) ∧
      final.global.length = global.length ∧ final.shared.length = shared.length ∧
      final.barrier = Barrier.reset (s.depth+1) ∧ final.site = none ∧
      (∀ event ∈ events, AccessSafe (Dense.initial s global shared seeds) event) := by
  obtain ⟨events,final,run,source,co,valid,grounded,done,values,inputs,gl,sl,barrier,site,safe,_⟩ :=
    Dense.selected_forward_admitted s bounds global shared seeds globalBound sharedBound
  refine ⟨events,final,run,source,co,valid,grounded,done,?_,inputs,gl,sl,barrier,site,safe⟩
  intro row
  exact ⟨Dense.forwardWord s global row.val,values row.val row.isLt,forward_word_accuracy encoding row⟩

end PtxTorchLean.DenseForward

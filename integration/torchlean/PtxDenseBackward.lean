import PtxDenseForward
import PtxBinary32.DenseBackwardStorage

/-! Numerical correspondence of the actual parallel backward launches with the
actual TorchLean generated VJP. Finite-range and branch-margin guards concern
initial encodings and the specified rounding order, not unknown execution values. -/
namespace PtxTorchLean.DenseBackward
open Ptx Ptx.Binary32 Ptx.Scalar.Parallel
open TorchLean TorchLean.Tensor
abbrev Shape := Ptx.Scalar.Parallel.DenseBackward.Shape

structure Encoding (s : Shape) (memory : List Word) (incoming : Fin s.rows → Word)
    (x : Tensor ℝ (DenseVJP.column s.columns))
    (w : Tensor ℝ (DenseVJP.matrix s.rows s.columns))
    (bias d : Tensor ℝ (DenseVJP.column s.rows)) where
  forward : DenseForward.Encoding s.forward memory x w bias
  seedValue : Fin s.rows → ℝ
  seedError : Fin s.rows → ℝ
  seedReal : ∀ r, finiteReal (incoming r)=some (seedValue r)
  seedApprox : ∀ r, |seedValue r-Spec.get2 d r 0|≤seedError r
  margin : ∀ r, (forward.row r).error < |(forward.row r).idealAffine|

variable {s : Shape} {memory : List Word} {incoming : Fin s.rows → Word}
  {x : Tensor ℝ (DenseVJP.column s.columns)} {w : Tensor ℝ (DenseVJP.matrix s.rows s.columns)}
  {bias d : Tensor ℝ (DenseVJP.column s.rows)}

def Encoding.gWord (_i : Encoding s memory incoming x w bias d) (r : Fin s.rows) : Word :=
  Relu.gate (Dense.forwardWord s.forward memory r.val) (incoming r)
noncomputable def Encoding.gReal (i : Encoding s memory incoming x w bias d) (r : Fin s.rows) : ℝ :=
  if 0<(i.forward.row r).affine then i.seedValue r else 0
noncomputable def Encoding.gIdeal (i : Encoding s memory incoming x w bias d) (r : Fin s.rows) : ℝ :=
  if 0<(i.forward.row r).idealAffine then Spec.get2 d r 0 else 0

theorem Encoding.g_real (i : Encoding s memory incoming x w bias d) (r : Fin s.rows) :
    finiteReal (i.gWord r)=some (i.gReal r) := by
  have real := (DenseForward.forward_word_accuracy i.forward r).1
  have gate := Relu.gate_real _ _ _ _ real (i.seedReal r)
  simpa [Encoding.gWord,Encoding.gReal,lt_max_iff] using gate

theorem Encoding.affine_accuracy (i : Encoding s memory incoming x w bias d) (r : Fin s.rows) :
    |(i.forward.row r).affine-(i.forward.row r).idealAffine|≤(i.forward.row r).error := by
  apply (Reduction.row_affine_accuracy (i.forward.row r) (a := Dense.affineWord s.forward memory r.val) ?_).2
  refine ⟨Dense.nodeValue s.forward memory r.val s.forward.depth 0,?_,envelope_self _⟩
  rw [i.forward.row_words]
  simpa using Dense.node_tree s.forward memory r.val s.forward.depth 0

theorem Encoding.g_error (i : Encoding s memory incoming x w bias d) (r : Fin s.rows) :
    |i.gReal r-i.gIdeal r|≤ i.seedError r := by
  have stable := Relu.sign_stable _ _ _ (i.affine_accuracy r) (i.margin r)
  have nonnegative : 0≤ i.seedError r := (abs_nonneg _).trans (i.seedApprox r)
  by_cases positive : 0<(i.forward.row r).idealAffine <;>
    simp [Encoding.gReal,Encoding.gIdeal,stable,positive,i.seedApprox,nonnegative]

theorem Encoding.g_ideal (i : Encoding s memory incoming x w bias d) (r : Fin s.rows) :
    i.gIdeal r=Spec.get2 (DenseVJP.gate (DenseVJP.affine x w bias) d) r 0 := by
  rw [DenseVJP.gate_coordinate]
  unfold Encoding.gIdeal ReluVJP.gate
  rw [i.forward.row_ideal]

theorem stored_gate (i : Encoding s memory incoming x w bias d) {bounds : Ptx.Scalar.Parallel.DenseBackward.Bounds s}
    (e : Ptx.Scalar.Parallel.DenseBackward.Execution s bounds memory incoming)
    (size : memory.length=s.forward.globalWords) (r : Fin s.rows) : e.g r=i.gWord r := by
  obtain ⟨value,saved,correct⟩ := (Dense.launch_correct e.forwardRun).1 r
  have real := (DenseForward.output_accuracy i.forward r value correct).1
  have actual : finiteReal e.forward[s.forward.outputBase+r.val]! =some (max (i.forward.row r).affine 0) := by
    simpa [List.getElem!_eq_getElem?_getD,saved] using real
  have referenceReal := (DenseForward.forward_word_accuracy i.forward r).1
  rw [Ptx.Scalar.Parallel.DenseBackward.gate_result e size r]
  simp only [Encoding.gWord,Relu.gate,Relu.positive_iff _ _ actual,Relu.positive_iff _ _ referenceReal]

/-- These multiplication ranges are computed from original encoded real values
and the recomputed activation, before examining any candidate execution. -/
structure ProductRanges (i : Encoding s memory incoming x w bias d) : Prop where
  weight : ∀ r c, |i.gReal r*(i.forward.entry r c).rh|≤Bounds.maxFinite
  input : ∀ r c, |(i.forward.entry r c).lh*i.gReal r|≤Bounds.maxFinite

noncomputable def weightEntry (i : Encoding s memory incoming x w bias d) (range : ProductRanges i)
    (r : Fin s.rows) (c : Fin s.columns) : DotError.Input where
  left := i.gWord r
  right := memory[c.val]!
  lh := i.gReal r
  rh := (i.forward.entry r c).rh
  l := i.gIdeal r
  r := Spec.get2 x c 0
  el := i.seedError r
  er := (i.forward.entry r c).er
  leftReal := i.g_real r
  rightReal := by rw [← i.forward.inputWord r c]; exact (i.forward.entry r c).rightReal
  leftError := i.g_error r
  rightError := by rw [← i.forward.inputIdeal r c]; exact (i.forward.entry r c).rightError
  productRange := range.weight r c

noncomputable def inputEntry (i : Encoding s memory incoming x w bias d) (range : ProductRanges i)
    (c : Fin s.columns) (r : Fin s.rows) : DotError.Input where
  left := memory[s.forward.weight r.val c.val]!
  right := i.gWord r
  lh := (i.forward.entry r c).lh
  rh := i.gReal r
  l := Spec.get2 w r c
  r := i.gIdeal r
  el := (i.forward.entry r c).el
  er := i.seedError r
  leftReal := by rw [← i.forward.weightWord r c]; exact (i.forward.entry r c).leftReal
  rightReal := i.g_real r
  leftError := by rw [← i.forward.weightIdeal r c]; exact (i.forward.entry r c).leftError
  rightError := i.g_error r
  productRange := range.input r c

noncomputable def inputTree (i : Encoding s memory incoming x w bias d) (range : ProductRanges i)
    (c : Fin s.columns) : Reduction.Tree DotError.Input :=
  Reduction.balanced s.depth 0 (Reduction.paddedInput (inputEntry i range c))

structure Ranges (i : Encoding s memory incoming x w bias d) where
  products : ProductRanges i
  tree : ∀ c, Reduction.Safe (inputTree i products c)
  bias : ∀ c, |Reduction.rounded (inputTree i products c)+0|≤Bounds.maxFinite

noncomputable def inputRow (i : Encoding s memory incoming x w bias d) (range : Ranges i)
    (c : Fin s.columns) : Reduction.RowInput where
  tree := inputTree i range.products c
  safe := range.tree c
  bias := 0
  bh := 0
  b := 0
  eb := 0
  biasReal := Relu.zero_real
  biasError := by simp
  additionRange := range.bias c

theorem input_words (i : Encoding s memory incoming x w bias d) (range : Ranges i)
    {bounds : Ptx.Scalar.Parallel.DenseBackward.Bounds s}
    (e : Ptx.Scalar.Parallel.DenseBackward.Execution s bounds memory incoming)
    (size : memory.length=s.forward.globalWords) (c : Fin s.columns) :
    Reduction.words (inputRow i range c).tree=
      Reduction.balanced s.transposed.depth 0 (Dense.operands s.transposed (Ptx.Scalar.Parallel.DenseBackward.packet s e.copied) c.val) := by
  unfold inputRow inputTree Reduction.words
  rw [Reduction.map_balanced]
  apply congrArg (Reduction.balanced s.depth 0)
  funext r
  by_cases h : r<s.rows
  · simp only [Reduction.paddedInput,Dense.operands,show s.transposed.columns=s.rows from rfl,h,↓reduceDIte,↓reduceIte,inputEntry]
    rw [Ptx.Scalar.Parallel.DenseBackward.packet_weight e size c ⟨r,h⟩,
      Ptx.Scalar.Parallel.DenseBackward.packet_input e size ⟨r,h⟩,stored_gate i e size ⟨r,h⟩]

  · simp [Reduction.paddedInput,h,Dense.operands,Ptx.Scalar.Parallel.DenseBackward.Shape.transposed,Reduction.zeroInput]

theorem input_ideal (i : Encoding s memory incoming x w bias d) (range : Ranges i) (c : Fin s.columns) :
    (inputRow i range c).idealAffine=
      Spec.get2 (TorchLean.TensorPack.get ((DenseVJP.graph s.rows s.columns).vjpWithSeed (DenseVJP.inputs x w bias) d) 0) c 0 := by
  rw [(DenseVJP.backward_coordinates x w bias d).1 c]
  unfold Reduction.RowInput.idealAffine inputRow inputTree
  rw [Reduction.padded_ideal _ _ s.padded]
  simp [inputEntry,i.g_ideal]

theorem weight_accuracy (i : Encoding s memory incoming x w bias d) (range : Ranges i)
    {bounds : Ptx.Scalar.Parallel.DenseBackward.Bounds s}
    (e : Ptx.Scalar.Parallel.DenseBackward.Execution s bounds memory incoming)
    (size : memory.length=s.forward.globalWords) (r : Fin s.rows) (c : Fin s.columns) :
    finiteReal (e.dw r c)=some (Reduction.rounded (.leaf (weightEntry i range.products r c))) ∧
      |Reduction.rounded (.leaf (weightEntry i range.products r c))-
        Spec.get2 (TorchLean.TensorPack.get ((DenseVJP.graph s.rows s.columns).vjpWithSeed (DenseVJP.inputs x w bias) d) 1) r c|≤
        Reduction.budget (.leaf (weightEntry i range.products r c)) := by
  have permitted := Ptx.Scalar.Parallel.DenseBackward.weight_result e size r c
  rw [stored_gate i e size r] at permitted
  have accuracy := Reduction.accuracy (.leaf (weightEntry i range.products r c)) trivial (Reduction.Eval.leaf permitted)
  refine ⟨accuracy.1,?_⟩
  rw [(DenseVJP.backward_coordinates x w bias d).2.1 r c]
  simpa [Reduction.ideal,weightEntry,i.g_ideal] using accuracy.2

theorem input_accuracy (i : Encoding s memory incoming x w bias d) (range : Ranges i)
    {bounds : Ptx.Scalar.Parallel.DenseBackward.Bounds s}
    (e : Ptx.Scalar.Parallel.DenseBackward.Execution s bounds memory incoming)
    (size : memory.length=s.forward.globalWords) (c : Fin s.columns) :
    finiteReal (e.dx c)=some (inputRow i range c).affine ∧
      |(inputRow i range c).affine-
        Spec.get2 (TorchLean.TensorPack.get ((DenseVJP.graph s.rows s.columns).vjpWithSeed (DenseVJP.inputs x w bias) d) 0) c 0|≤
        (inputRow i range c).error := by
  obtain ⟨dot,affine,node,addition,value⟩ := Ptx.Scalar.Parallel.DenseBackward.input_result e c
  have eq : e.dx c=affine := by simpa [Dense.activate,Ptx.Scalar.Parallel.DenseBackward.Shape.transposed] using value
  have allowed : Reduction.RowEval (inputRow i range c) (e.dx c) := by
    refine ⟨dot,?_,?_⟩
    · rw [input_words i range e size c]
      simpa [Dense.Node] using node
    · rw [eq]
      simpa [inputRow,Ptx.Scalar.Parallel.DenseBackward.packet_bias e size c] using addition
  have accuracy := Reduction.row_affine_accuracy (inputRow i range c) allowed
  exact ⟨accuracy.1,by simpa [input_ideal i range c] using accuracy.2⟩

theorem bias_accuracy (i : Encoding s memory incoming x w bias d)
    {bounds : Ptx.Scalar.Parallel.DenseBackward.Bounds s}
    (e : Ptx.Scalar.Parallel.DenseBackward.Execution s bounds memory incoming)
    (size : memory.length=s.forward.globalWords) (r : Fin s.rows) :
    finiteReal (e.g r)=some (i.gReal r) ∧
      |i.gReal r-Spec.get2 (TorchLean.TensorPack.get
        ((DenseVJP.graph s.rows s.columns).vjpWithSeed (DenseVJP.inputs x w bias) d) 2) r 0|≤ i.seedError r := by
  rw [stored_gate i e size r,(DenseVJP.backward_coordinates x w bias d).2.2 r]
  exact ⟨i.g_real r,by simpa [i.g_ideal r] using i.g_error r⟩


/-- The margin excludes every ReLU corner of the actual real graph. -/
theorem Encoding.away (i : Encoding s memory incoming x w bias d) (r : Fin s.rows) :
    Spec.get2 (DenseVJP.affine x w bias) r 0≠0 := by
  rw [← i.forward.row_ideal]
  intro zero
  have margin := i.margin r
  have nonnegative := (abs_nonneg _).trans (i.affine_accuracy r)
  rw [zero,abs_zero] at margin
  linarith

/-- Stored arrays and explicit error bounds against the three tensors returned
by TorchLean's actual generated backward. Bias gradients share the gated buffer. -/
def Correct (i : Encoding s memory incoming x w bias d) (range : Ranges i)
    {bounds : Ptx.Scalar.Parallel.DenseBackward.Bounds s}
    (e : Ptx.Scalar.Parallel.DenseBackward.Execution s bounds memory incoming) : Prop :=
  let backward := (DenseVJP.graph s.rows s.columns).vjpWithSeed (DenseVJP.inputs x w bias) d
  (∀ r, e.gated[s.gateBase+r.val]?=some (e.g r) ∧ finiteReal (e.g r)=some (i.gReal r) ∧
    |i.gReal r-Spec.get2 (TorchLean.TensorPack.get backward 2) r 0|≤ i.seedError r) ∧
  (∀ r c, e.weighted[s.weightBase+r.val*s.columns+c.val]?=some (e.dw r c) ∧
    finiteReal (e.dw r c)=some (Reduction.rounded (.leaf (weightEntry i range.products r c))) ∧
    |Reduction.rounded (.leaf (weightEntry i range.products r c))-Spec.get2 (TorchLean.TensorPack.get backward 1) r c|≤
      Reduction.budget (.leaf (weightEntry i range.products r c))) ∧
  (∀ c, e.inputGradient[s.transposed.outputBase+c.val]?=some (e.dx c) ∧
    finiteReal (e.dx c)=some (inputRow i range c).affine ∧
    |(inputRow i range c).affine-Spec.get2 (TorchLean.TensorPack.get backward 0) c 0|≤ (inputRow i range c).error) ∧
  (∀ index, index<s.forward.outputBase → e.weighted[index]?=memory[index]?)

/-- Quantifies over every admitted completed execution of every stage, including
its actual stored handoffs. The same theorem includes empty dimensions. -/
theorem universal_backward (i : Encoding s memory incoming x w bias d) (range : Ranges i)
    {bounds : Ptx.Scalar.Parallel.DenseBackward.Bounds s}
    (e : Ptx.Scalar.Parallel.DenseBackward.Execution s bounds memory incoming)
    (size : memory.length=s.forward.globalWords) : Correct i range e := by
  have stored := Ptx.Scalar.Parallel.DenseBackward.gradients_stored e size
  exact ⟨fun r => ⟨stored.1 r,bias_accuracy i e size r⟩,
    (fun r c => ⟨stored.2.1 r c,weight_accuracy i range e size r c⟩),
    (fun c => ⟨stored.2.2 c,input_accuracy i range e size c⟩),
    Ptx.Scalar.Parallel.DenseBackward.input_frame e size⟩

/-- Nonvacuity: all stages admit a completed execution, and its stored gradients
satisfy the numerical contract. Numerical assumptions are not needed to construct
the execution itself; they justify its interpretation as a real-network backward. -/
theorem backward_exists (i : Encoding s memory incoming x w bias d) (range : Ranges i)
    (bounds : Ptx.Scalar.Parallel.DenseBackward.Bounds s) (size : memory.length=s.forward.globalWords) :
    ∃ e : Ptx.Scalar.Parallel.DenseBackward.Execution s bounds memory incoming, Correct i range e := by
  obtain ⟨e⟩ := Ptx.Scalar.Parallel.DenseBackward.execution_exists s bounds memory incoming size
  exact ⟨e,universal_backward i range e size⟩


end PtxTorchLean.DenseBackward

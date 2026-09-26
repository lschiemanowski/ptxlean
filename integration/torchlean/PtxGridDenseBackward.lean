import PtxDenseBackward
import PtxBinary32.GridDenseBackwardStorage

/-! Grid forward/backward launches use the existing numerical encoding, range
and ReLU-margin policy. These theorems concern actual stored handoffs and the
actual TorchLean generated VJP, separately from finite execution existence. -/
namespace PtxTorchLean.GridDenseBackward
open Ptx Ptx.Binary32 Ptx.Scalar.Parallel
open TorchLean TorchLean.Tensor
open PtxTorchLean.DenseBackward
variable {s : Ptx.Scalar.Parallel.DenseBackward.Shape} {memory : List Word} {incoming : Fin s.rows → Word}
  {x : Tensor ℝ (DenseVJP.column s.columns)} {w : Tensor ℝ (DenseVJP.matrix s.rows s.columns)}
  {bias d : Tensor ℝ (DenseVJP.column s.rows)}

theorem stored_gate (i : Encoding s memory incoming x w bias d) {bounds : Ptx.Scalar.Parallel.GridDenseBackward.Bounds s}
    (e : Ptx.Scalar.Parallel.GridDenseBackward.Execution s bounds memory incoming)
    (size : memory.length=s.forward.globalWords) (r : Fin s.rows) : e.g r=i.gWord r := by
  obtain ⟨value,saved,correct⟩ := (GridDense.launch_correct e.forwardRun).1 r
  have real := (DenseForward.output_accuracy i.forward r value correct).1
  have actual : finiteReal e.forward[s.forward.outputBase+r.val]! =some (max (i.forward.row r).affine 0) := by
    simpa [List.getElem!_eq_getElem?_getD,saved] using real
  have referenceReal := (DenseForward.forward_word_accuracy i.forward r).1
  rw [Ptx.Scalar.Parallel.GridDenseBackward.gate_result e size r]
  simp only [Encoding.gWord,Relu.gate,Relu.positive_iff _ _ actual,Relu.positive_iff _ _ referenceReal]


theorem input_words (i : Encoding s memory incoming x w bias d) (range : Ranges i)
    {bounds : Ptx.Scalar.Parallel.GridDenseBackward.Bounds s}
    (e : Ptx.Scalar.Parallel.GridDenseBackward.Execution s bounds memory incoming)
    (size : memory.length=s.forward.globalWords) (c : Fin s.columns) :
    Reduction.words (inputRow i range c).tree=
      Reduction.balanced s.transposed.depth 0 (Dense.operands s.transposed (Ptx.Scalar.Parallel.GridDenseBackward.packet s e.copied) c.val) := by
  unfold inputRow inputTree Reduction.words
  rw [Reduction.map_balanced]
  apply congrArg (Reduction.balanced s.depth 0)
  funext r
  by_cases h : r<s.rows
  · simp only [Reduction.paddedInput,Dense.operands,show s.transposed.columns=s.rows from rfl,h,↓reduceDIte,↓reduceIte,inputEntry]
    rw [Ptx.Scalar.Parallel.GridDenseBackward.packet_weight e size c ⟨r,h⟩,
      Ptx.Scalar.Parallel.GridDenseBackward.packet_input e size ⟨r,h⟩,stored_gate i e size ⟨r,h⟩]

  · simp [Reduction.paddedInput,h,Dense.operands,Ptx.Scalar.Parallel.DenseBackward.Shape.transposed,Reduction.zeroInput]


theorem weight_accuracy (i : Encoding s memory incoming x w bias d) (range : Ranges i)
    {bounds : Ptx.Scalar.Parallel.GridDenseBackward.Bounds s}
    (e : Ptx.Scalar.Parallel.GridDenseBackward.Execution s bounds memory incoming)
    (size : memory.length=s.forward.globalWords) (r : Fin s.rows) (c : Fin s.columns) :
    finiteReal (e.dw r c)=some (Reduction.rounded (.leaf (weightEntry i range.products r c))) ∧
      |Reduction.rounded (.leaf (weightEntry i range.products r c))-
        Spec.get2 (TorchLean.TensorPack.get ((DenseVJP.graph s.rows s.columns).vjpWithSeed (DenseVJP.inputs x w bias) d) 1) r c|≤
        Reduction.budget (.leaf (weightEntry i range.products r c)) := by
  have permitted := Ptx.Scalar.Parallel.GridDenseBackward.weight_result e size r c
  rw [stored_gate i e size r] at permitted
  have accuracy := Reduction.accuracy (.leaf (weightEntry i range.products r c)) trivial (Reduction.Eval.leaf permitted)
  refine ⟨accuracy.1,?_⟩
  rw [(DenseVJP.backward_coordinates x w bias d).2.1 r c]
  simpa [Reduction.ideal,weightEntry,i.g_ideal] using accuracy.2

theorem input_accuracy (i : Encoding s memory incoming x w bias d) (range : Ranges i)
    {bounds : Ptx.Scalar.Parallel.GridDenseBackward.Bounds s}
    (e : Ptx.Scalar.Parallel.GridDenseBackward.Execution s bounds memory incoming)
    (size : memory.length=s.forward.globalWords) (c : Fin s.columns) :
    finiteReal (e.dx c)=some (inputRow i range c).affine ∧
      |(inputRow i range c).affine-
        Spec.get2 (TorchLean.TensorPack.get ((DenseVJP.graph s.rows s.columns).vjpWithSeed (DenseVJP.inputs x w bias) d) 0) c 0|≤
        (inputRow i range c).error := by
  obtain ⟨dot,affine,node,addition,value⟩ := Ptx.Scalar.Parallel.GridDenseBackward.input_result e c
  have eq : e.dx c=affine := by simpa [Dense.activate,Ptx.Scalar.Parallel.DenseBackward.Shape.transposed] using value
  have allowed : Reduction.RowEval (inputRow i range c) (e.dx c) := by
    refine ⟨dot,?_,?_⟩
    · rw [input_words i range e size c]
      simpa [Dense.Node] using node
    · rw [eq]
      simpa [inputRow,Ptx.Scalar.Parallel.GridDenseBackward.packet_bias e size c] using addition
  have accuracy := Reduction.row_affine_accuracy (inputRow i range c) allowed
  exact ⟨accuracy.1,by simpa [input_ideal i range c] using accuracy.2⟩

theorem bias_accuracy (i : Encoding s memory incoming x w bias d)
    {bounds : Ptx.Scalar.Parallel.GridDenseBackward.Bounds s}
    (e : Ptx.Scalar.Parallel.GridDenseBackward.Execution s bounds memory incoming)
    (size : memory.length=s.forward.globalWords) (r : Fin s.rows) :
    finiteReal (e.g r)=some (i.gReal r) ∧
      |i.gReal r-Spec.get2 (TorchLean.TensorPack.get
        ((DenseVJP.graph s.rows s.columns).vjpWithSeed (DenseVJP.inputs x w bias) d) 2) r 0|≤ i.seedError r := by
  rw [stored_gate i e size r,(DenseVJP.backward_coordinates x w bias d).2.2 r]
  exact ⟨i.g_real r,by simpa [i.g_ideal r] using i.g_error r⟩



/-- Stored arrays and explicit error bounds against the three tensors returned
by TorchLean's actual generated backward. Bias gradients share the gated buffer. -/
def Correct (i : Encoding s memory incoming x w bias d) (range : Ranges i)
    {bounds : Ptx.Scalar.Parallel.GridDenseBackward.Bounds s}
    (e : Ptx.Scalar.Parallel.GridDenseBackward.Execution s bounds memory incoming) : Prop :=
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
    {bounds : Ptx.Scalar.Parallel.GridDenseBackward.Bounds s}
    (e : Ptx.Scalar.Parallel.GridDenseBackward.Execution s bounds memory incoming)
    (size : memory.length=s.forward.globalWords) : Correct i range e := by
  have stored := Ptx.Scalar.Parallel.GridDenseBackward.gradients_stored e size
  exact ⟨fun r => ⟨stored.1 r,bias_accuracy i e size r⟩,
    (fun r c => ⟨stored.2.1 r c,weight_accuracy i range e size r c⟩),
    (fun c => ⟨stored.2.2 c,input_accuracy i range e size c⟩),
    Ptx.Scalar.Parallel.GridDenseBackward.input_frame e size⟩

/-- Nonvacuity: all stages admit a completed execution, and its stored gradients
satisfy the numerical contract. Numerical assumptions are not needed to construct
the execution itself; they justify its interpretation as a real-network backward. -/
theorem backward_exists (i : Encoding s memory incoming x w bias d) (range : Ranges i)
    (bounds : Ptx.Scalar.Parallel.GridDenseBackward.Bounds s) (size : memory.length=s.forward.globalWords) :
    ∃ e : Ptx.Scalar.Parallel.GridDenseBackward.Execution s bounds memory incoming, Correct i range e := by
  obtain ⟨e⟩ := Ptx.Scalar.Parallel.GridDenseBackward.execution_exists s bounds memory incoming size
  exact ⟨e,universal_backward i range e size⟩



end PtxTorchLean.GridDenseBackward

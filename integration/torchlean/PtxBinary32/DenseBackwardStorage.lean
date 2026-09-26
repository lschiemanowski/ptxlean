import PtxBinary32.DenseBackwardLayout

namespace Ptx.Scalar.Parallel.DenseBackward
open Ptx.Binary32

variable {s : Shape} {b : Bounds s} {before : List Word} {incoming : Fin s.rows → Word}

def Execution.g (e : Execution s b before incoming) (r : Fin s.rows) : Word := e.gated[s.gateBase+r.val]!
def Execution.dw (e : Execution s b before incoming) (r : Fin s.rows) (c : Fin s.columns) : Word :=
  e.weighted[s.weightBase+r.val*s.columns+c.val]!
def Execution.dx (e : Execution s b before incoming) (c : Fin s.columns) : Word :=
  e.inputGradient[s.transposed.outputBase+c.val]!

theorem lengths (e : Execution s b before incoming) (size : before.length=s.forward.globalWords) :
    e.forward.length=s.forward.globalWords ∧ e.gated.length=s.weightBase ∧
    e.weighted.length=s.copyBase-1 ∧ e.copied.length=s.copyBase+s.transposed.globalWords ∧
    (packet s e.copied).length=s.transposed.globalWords ∧ e.inputGradient.length=s.transposed.globalWords := by
  have fl := (Dense.launch_correct e.forwardRun).2.2
  have gl := (Pointwise.launch_correct e.gateRun).2.2
  have wl := (Pointwise.launch_correct e.weightRun).2.2
  have cl := (Pointwise.launch_correct e.copyRun).2.2
  have il := (Dense.launch_correct e.inputRun).2.2
  simp only [gateInput,weightInput,copyInput,List.length_append,List.length_ofFn,List.length_replicate,List.length_cons,List.length_nil] at gl wl cl
  simp only [packet,List.length_drop] at il
  simp only [packet,List.length_drop,Shape.copyBase,Shape.weightBase,Shape.gateBase] at *
  omega

private theorem bang_eq (a b : List Word) (i : Nat) (h : a[i]?=b[i]?) : a[i]! =b[i]! := by
  simpa [List.getElem!_eq_getElem?_getD] using congrArg (fun x => x.getD (default : Word)) h

private theorem saved_word (a : List Word) (i : Nat) (value : Word) (h : a[i]?=some value) : a[i]! =value := by
  simp [List.getElem!_eq_getElem?_getD,h]

theorem input_frame (e : Execution s b before incoming) (size : before.length=s.forward.globalWords)
    (i : Nat) (hi : i<s.forward.outputBase) : e.weighted[i]?=before[i]? := by
  have ls := lengths e size
  have fi := (Dense.launch_correct e.forwardRun).2.1 i hi
  have gb : i<(gateLayout s b).prefixWords := by change i<s.gateBase; unfold Shape.gateBase Dense.Shape.globalWords; omega
  have wb : i<(weightLayout s b).prefixWords := by change i<s.weightBase; unfold Shape.weightBase Shape.gateBase Dense.Shape.globalWords; omega
  have gi := (Pointwise.launch_correct e.gateRun).2.1 i gb
  have wi := (Pointwise.launch_correct e.weightRun).2.1 i wb
  have inF : i<e.forward.length := by rw [ls.1]; unfold Dense.Shape.globalWords; omega
  have inG : i<e.gated.length := by rw [ls.2.1]; exact wb
  change e.weighted[i]?=(e.gated++List.replicate s.weightCount 0)[i]? at wi
  rw [List.getElem?_append_left inG] at wi
  simp only [gateInput,List.append_assoc] at gi
  rw [List.getElem?_append_left inF] at gi
  exact wi.trans (gi.trans fi)

theorem gate_frame (e : Execution s b before incoming) (size : before.length=s.forward.globalWords)
    (r : Fin s.rows) : e.weighted[s.gateBase+r.val]! =e.g r := by
  have ls := lengths e size
  have bound : s.gateBase+r.val<s.weightBase := by have := r.isLt; unfold Shape.weightBase; omega
  have eq := (Pointwise.launch_correct e.weightRun).2.1 (s.gateBase+r.val) bound
  apply bang_eq
  simpa [weightInput,List.getElem?_append,ls.2.1,bound,Execution.g] using eq

theorem gate_result (e : Execution s b before incoming) (size : before.length=s.forward.globalWords)
    (r : Fin s.rows) : e.g r=Relu.gate e.forward[s.forward.outputBase+r.val]! (incoming r) := by
  have ls := lengths e size
  obtain ⟨value,saved,correct⟩ := (Pointwise.launch_correct e.gateRun).1 r
  have saved' : e.g r=value := saved_word _ _ _ saved
  rw [saved']
  change value=Relu.gate _ _ at correct
  have leftBound : s.forward.outputBase+r.val<e.forward.length := by rw [ls.1]; have hr : r.val<s.forward.rows := r.isLt; unfold Dense.Shape.globalWords; omega
  have rightBound : r.val<s.rows := r.isLt
  simp only [gateInput,List.append_assoc] at correct
  have leftBound' : s.forward.outputBase+r.val<s.forward.globalWords := by rw [← ls.1]; exact leftBound
  simpa only [gateLayout,gateInput,List.getElem!_eq_getElem?_getD,List.getElem?_append,ls.1,leftBound',rightBound,↓reduceIte,Nat.add_sub_cancel_left,List.getElem?_ofFn,List.length_ofFn,dite_true,Option.getD_some,show ¬s.forward.globalWords+r.val<s.forward.globalWords by omega] using correct

theorem weight_result (e : Execution s b before incoming) (size : before.length=s.forward.globalWords)
    (r : Fin s.rows) (c : Fin s.columns) : Results .mul (e.g r) before[c.val]! (e.dw r c) := by
  have pos : 0<s.columns := by have := c.isLt; omega
  let t : Fin s.weightCount := ⟨r.val*s.columns+c.val,by
    change r.val*s.columns+c.val<s.rows*s.columns
    have bound := Nat.mul_le_mul_right s.columns r.isLt
    rw [Nat.succ_mul] at bound
    have := c.isLt
    omega⟩
  have row : t.val/s.columns=r.val := by
    change (r.val*s.columns+c.val)/s.columns=r.val
    rw [Nat.add_comm,Nat.add_mul_div_right _ _ pos,Nat.div_eq_of_lt c.isLt,Nat.zero_add]
  have col : t.val%s.columns=c.val := by simp [t,Nat.add_mod,Nat.mod_eq_of_lt c.isLt]
  have ls := lengths e size
  obtain ⟨value,saved,correct⟩ := (Pointwise.launch_correct e.weightRun).1 t
  have saved' : e.dw r c=value := saved_word _ _ _ (by simpa [Pointwise.Layout.output,weightLayout,t,Nat.add_assoc] using saved)
  rw [saved']
  change Results .mul (weightInput s e.gated)[s.gateBase+t.val/s.columns]!
    (weightInput s e.gated)[t.val%s.columns]! value at correct
  rw [row,col] at correct
  have gateBound : s.gateBase+r.val<e.gated.length := by rw [ls.2.1]; have := r.isLt; unfold Shape.weightBase; omega
  have inputBound : c.val<s.forward.outputBase := by have := c.isLt; change c.val<s.columns+s.rows*s.columns+s.rows; omega
  have inputG : c.val<e.gated.length := by rw [ls.2.1]; unfold Shape.weightBase Shape.gateBase Dense.Shape.globalWords; omega
  have gi := (Pointwise.launch_correct e.gateRun).2.1 c.val (show c.val<s.gateBase by unfold Shape.gateBase Dense.Shape.globalWords; omega)
  have fi := (Dense.launch_correct e.forwardRun).2.1 c.val inputBound
  have inputF : c.val<e.forward.length := by rw [ls.1]; unfold Dense.Shape.globalWords; omega
  have eq : e.gated[c.val]?=before[c.val]? := by
    simp only [gateInput,List.append_assoc] at gi
    rw [List.getElem?_append_left inputF] at gi
    exact gi.trans fi
  simpa only [weightInput,List.getElem!_eq_getElem?_getD,List.getElem?_append,gateBound,inputG,↓reduceIte,eq,Execution.g] using correct

theorem packet_word (e : Execution s b before incoming) (j : Fin s.transposed.globalWords) :
    (packet s e.copied)[j.val]?=some ((copyInput s e.weighted)[copySource s j.val]!) := by
  obtain ⟨value,saved,correct⟩ := (Pointwise.launch_correct e.copyRun).1 j
  change value=(copyInput s e.weighted)[copySource s j.val]! at correct
  simpa [packet,List.getElem?_drop,copyLayout,Pointwise.Layout.output,correct,Nat.add_comm] using saved

private theorem copied_prefix (e : Execution s b before incoming) (j : Fin s.transposed.globalWords)
    (bound : copySource s j.val<e.weighted.length) :
    (packet s e.copied)[j.val]! =e.weighted[copySource s j.val]! := by
  have h := packet_word e j
  have src : (copyInput s e.weighted)[copySource s j.val]! =e.weighted[copySource s j.val]! := by
    apply bang_eq
    simp only [copyInput,List.append_assoc]
    exact List.getElem?_append_left bound
  exact (saved_word _ _ _ h).trans src

theorem packet_input (e : Execution s b before incoming) (size : before.length=s.forward.globalWords)
    (r : Fin s.rows) : (packet s e.copied)[r.val]! =e.g r := by
  have fit : r.val<s.transposed.globalWords := by
    have := r.isLt
    change r.val<s.rows+s.columns*s.rows+s.columns+s.columns
    omega
  have src : copySource s r.val=s.gateBase+r.val := by simp [copySource,r.isLt]
  have bound : copySource s r.val<e.weighted.length := by
    rw [src,(lengths e size).2.2.1]
    have := r.isLt
    unfold Shape.copyBase Shape.weightBase
    omega
  have h := copied_prefix e ⟨r.val,fit⟩ bound
  rw [src] at h
  exact h.trans (gate_frame e size r)

theorem packet_weight (e : Execution s b before incoming) (size : before.length=s.forward.globalWords)
    (c : Fin s.columns) (r : Fin s.rows) :
    (packet s e.copied)[s.transposed.weight c.val r.val]! =before[s.forward.weight r.val c.val]! := by
  have weight := Dense.weight_bound s.transposed c.val r.val c.isLt r.isLt
  have fit : s.transposed.weight c.val r.val<s.transposed.globalWords := by
    unfold Dense.Shape.globalWords Dense.Shape.outputBase
    omega
  have src : copySource s (s.transposed.weight c.val r.val)=s.forward.weight r.val c.val := by
    have pos : 0<s.rows := by have := r.isLt; omega
    have low : ¬s.transposed.weight c.val r.val<s.rows := by
      change ¬s.rows+c.val*s.rows+r.val<s.rows; omega
    simp only [copySource,low,ite_false,weight.2,ite_true]
    change s.forward.weight (((s.rows+c.val*s.rows+r.val)-s.rows)%s.rows)
      (((s.rows+c.val*s.rows+r.val)-s.rows)/s.rows)=s.forward.weight r.val c.val
    have sub : s.rows+c.val*s.rows+r.val-s.rows=c.val*s.rows+r.val := by omega
    rw [sub]
    have div : (c.val*s.rows+r.val)/s.rows=c.val := by
      rw [Nat.add_comm,Nat.add_mul_div_right _ _ pos,Nat.div_eq_of_lt r.isLt,Nat.zero_add]
    simp [Nat.add_mod,Nat.mod_eq_of_lt r.isLt,div]
  have original := Dense.weight_bound s.forward r.val c.val r.isLt c.isLt
  have inputBound : s.forward.weight r.val c.val<s.forward.outputBase := by
    unfold Dense.Shape.outputBase; omega
  have bound : copySource s (s.transposed.weight c.val r.val)<e.weighted.length := by
    rw [src,(lengths e size).2.2.1]
    unfold Shape.copyBase Shape.weightBase Shape.gateBase Dense.Shape.globalWords
    omega
  have h := copied_prefix e ⟨_,fit⟩ bound
  rw [src] at h
  exact h.trans (bang_eq _ _ _ (input_frame e size _ inputBound))

theorem packet_bias (e : Execution s b before incoming) (size : before.length=s.forward.globalWords)
    (c : Fin s.columns) : (packet s e.copied)[s.transposed.biasBase+c.val]! =0 := by
  have fit : s.transposed.biasBase+c.val<s.transposed.globalWords := by
    have := c.isLt
    change s.transposed.biasBase+c.val<s.transposed.biasBase+s.columns+s.columns
    omega
  have src : copySource s (s.transposed.biasBase+c.val)=s.copyBase-1 := by
    have low : ¬s.transposed.biasBase+c.val<s.rows := by
      change ¬s.rows+s.columns*s.rows+c.val<s.rows; omega
    simp [copySource,low]
  have h := packet_word e ⟨_,fit⟩
  have wl := (lengths e size).2.2.1
  have value : (copyInput s e.weighted)[copySource s (s.transposed.biasBase+c.val)]! =0 := by
    rw [src,← wl]
    simp [copyInput,List.getElem!_eq_getElem?_getD,List.getElem?_append]
  exact (saved_word _ _ _ h).trans value

theorem input_result (e : Execution s b before incoming) (c : Fin s.columns) :
    Dense.Output s.transposed (packet s e.copied) c.val (e.dx c) := by
  obtain ⟨value,saved,correct⟩ := (Dense.launch_correct e.inputRun).1 c
  have eq : e.dx c=value := saved_word _ _ _ saved
  rw [eq]; exact correct


private theorem present (words : List Word) (index : Nat) (bound : index<words.length) :
    words[index]?=some words[index]! := by
  simp [List.getElem!_eq_getElem?_getD,List.getElem?_eq_getElem bound]

theorem gradients_stored (e : Execution s b before incoming) (size : before.length=s.forward.globalWords) :
    (∀ r, e.gated[s.gateBase+r.val]?=some (e.g r)) ∧
    (∀ r c, e.weighted[s.weightBase+r.val*s.columns+c.val]?=some (e.dw r c)) ∧
    (∀ c, e.inputGradient[s.transposed.outputBase+c.val]?=some (e.dx c)) := by
  have ls := lengths e size
  refine ⟨?_,?_,?_⟩
  · intro r
    apply present
    rw [ls.2.1]
    have := r.isLt
    unfold Shape.weightBase; omega
  · intro r c
    apply present
    rw [ls.2.2.1]
    have bound := Nat.mul_le_mul_right s.columns r.isLt
    rw [Nat.succ_mul] at bound
    have := c.isLt
    unfold Shape.copyBase Shape.weightCount
    omega
  · intro c
    apply present
    rw [ls.2.2.2.2.2]
    have := c.isLt
    change s.transposed.outputBase+c.val<s.transposed.outputBase+s.columns
    omega


end Ptx.Scalar.Parallel.DenseBackward

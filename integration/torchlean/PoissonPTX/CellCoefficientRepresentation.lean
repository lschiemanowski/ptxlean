import PoissonPTX.CellWholeCorrespondence

namespace PtxTorchLean.Poisson.PTX.CoefficientRepresentation
open Concurrent.CellMiddle.Numeric

/-- Reindex the quadrature dimension using a proved equality of sizes. -/
def rows (same : q=n) (a : Mat Float q n) : Mat Float n n := same ▸ a
def square (same : q=n) (a : Mat Float q q) : Mat Float n n := same ▸ a

@[simp] theorem get_rows (same : q=n) (a : Mat Float q n) (i j : Fin n) :
    Spec.get2 (rows same a) i j=Spec.get2 a (Fin.cast same.symm i) j := by subst q; rfl
@[simp] theorem get_square (same : q=n) (a : Mat Float q q) (i j : Fin n) :
    Spec.get2 (square same a) i j=Spec.get2 a (Fin.cast same.symm i) (Fin.cast same.symm j) := by subst q; rfl

theorem local_action (same : q=n) (b d : Mat Float q n) (w : Mat Float q q) (u : Mat Float n n) :
    localAction (rows same b) (rows same d) (square same w) u=localAction b d w u := by subst q; rfl

/-- Each address contains one coefficient of the stated operator. No result,
intermediate tensor, execution or host-generation algorithm is stipulated. -/
structure Represents (o : Operator) (bases : Space → Word) (memory : Space → Memory) where
  shape : o.q.size=o.nodes.size
  b : ∀ i j : Fin o.nodes.size,
    decode (read64 (memory .global) (bases .global+BitVec.ofNat 64 ((i.val*o.nodes.size+j.val)*8)).toNat)=
      Spec.get2 o.b (Fin.cast shape.symm i) j
  d : ∀ i j : Fin o.nodes.size,
    decode (read64 (memory .global) (bases .global+BitVec.ofNat 64 (o.nodes.size*o.nodes.size*8+32+(i.val*o.nodes.size+j.val)*8)).toNat)=
      Spec.get2 o.d (Fin.cast shape.symm i) j
  w : ∀ i j : Fin o.nodes.size,
    decode (read64 (memory .global) (bases .global+BitVec.ofNat 64 (2*(o.nodes.size*o.nodes.size*8+32)+(i.val*o.nodes.size+j.val)*8)).toNat)=
      Spec.get2 o.w (Fin.cast shape.symm i) (Fin.cast shape.symm j)

theorem tensor_ext (a b : Mat Float n n) (h : ∀ i j, Spec.get2 a i j=Spec.get2 b i j) : a=b := by
  apply TorchLean.Tensor.Internal.Rep.ext
  rintro ⟨i,j,rest⟩; cases rest
  simpa [Spec.get2,Spec.get,TorchLean.Tensor.getScalar,TorchLean.Tensor.unstack,TorchLean.Tensor.item] using h i j

theorem tensors (r : Represents o bases memory) :
    initialTensor o.nodes.size bases memory .global 0=rows r.shape o.b ∧
    initialTensor o.nodes.size bases memory .global (o.nodes.size*o.nodes.size*8+32)=rows r.shape o.d ∧
    initialTensor o.nodes.size bases memory .global (2*(o.nodes.size*o.nodes.size*8+32))=square r.shape o.w := by
  refine ⟨tensor_ext _ _ ?_,tensor_ext _ _ ?_,tensor_ext _ _ ?_⟩
  all_goals intro i j
  · rw [get_rows]
    simpa [initialTensor,grid,matrix,Spec.get2,Spec.get,TorchLean.Tensor.getScalar,TorchLean.Tensor.unstack,TorchLean.Tensor.item,get_rows] using r.b i j
  · rw [get_rows]
    simpa [initialTensor,grid,matrix,Spec.get2,Spec.get,TorchLean.Tensor.getScalar,TorchLean.Tensor.unstack,TorchLean.Tensor.item,get_rows] using r.d i j
  · rw [get_square]
    simpa [initialTensor,grid,matrix,Spec.get2,Spec.get,TorchLean.Tensor.getScalar,TorchLean.Tensor.unstack,TorchLean.Tensor.item,get_square] using r.w i j

theorem calculation (r : Represents o bases memory) (u : Mat Float o.nodes.size o.nodes.size) :
    localAction (initialTensor o.nodes.size bases memory .global 0)
      (initialTensor o.nodes.size bases memory .global (o.nodes.size*o.nodes.size*8+32))
      (initialTensor o.nodes.size bases memory .global (2*(o.nodes.size*o.nodes.size*8+32))) u=
      localAction o.b o.d o.w u := by
  obtain ⟨b,d,w⟩ := tensors r
  rw [b,d,w,local_action]

end PtxTorchLean.Poisson.PTX.CoefficientRepresentation

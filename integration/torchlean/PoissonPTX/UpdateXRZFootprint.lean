import PoissonPTX.UpdateXRZAccess
import PoissonPTX.UpdateXRZArenaSafety

namespace PtxTorchLean.Poisson.PTX.UpdateXRZ
open Concurrent
variable {n : Nat} {a : Arena n} {memory : Memory} {regs : Fin n → Registers}
  {t : Fin n → Flow.State} {words : List (Event n)} {indices : List (Fin n × IndexSources.Access)}

def storePC : Field → Nat | .x => 23 | .r => 37 | .z => 52 | _ => 0
def readPC : Field → Nat | .p => 13 | .x => 17 | .ap => 27 | .r => 31 | .diagonal => 41 | .z => 0

theorem Arena.access_shape
    (shape : AccessAt (a.context thread) a.alpha (a.vector .p) (a.vector .x) (a.vector .ap)
      (a.vector .r) (a.vector .diagonal) a.boundary (a.vector .z) access) :
    access.space=.global ∧
    (if access.data.store then
       ∃ f, (f=Field.x ∨ f=Field.r ∨ f=Field.z) ∧ access.data.pc=storePC f ∧ access.data.address=a.slot f thread
     else (access.data.pc=9 ∧ access.data.address=a.base.toNat+a.alpha.toNat) ∨
       ∃ f, f≠Field.z ∧ access.data.pc=readPC f ∧ access.data.address=a.slot f thread) := by
  unfold AccessAt at shape
  change access.space=.global ∧ _ at shape
  have addressEq (f : Field) : (address64 (a.context thread).arena (Kernel.Residual.index (a.context thread)) (a.vector f)).toNat=a.slot f thread := a.vector_address thread f
  have scalarEq : ((a.context thread).arena+a.alpha).toNat=a.base.toNat+a.alpha.toNat := a.scalar_address
  simp only [addressEq,scalarEq] at shape
  refine ⟨shape.1,?_⟩
  by_cases writing : access.data.store=true
  · simp only [writing,↓reduceIte] at shape ⊢
    rcases shape.2 with hx|hr|hz
    · exact ⟨.x,by simp,hx⟩
    · exact ⟨.r,by simp,hr⟩
    · exact ⟨.z,by simp,hz⟩
  · simp only [writing] at shape ⊢
    rcases shape.2 with scalar|hp|hx|hap|hr|hd
    · exact Or.inl scalar
    · exact Or.inr ⟨.p,by decide,hp⟩
    · exact Or.inr ⟨.x,by decide,hx⟩
    · exact Or.inr ⟨.ap,by decide,hap⟩
    · exact Or.inr ⟨.r,by decide,hr⟩
    · exact Or.inr ⟨.diagonal,by decide,hd⟩

theorem Arena.parallel_access
    (run : Flow.Parallel.Runs a.context a.program (fun i => a.start memory (regs i)) words indices t)
    (member : Event.data thread access∈words) :
    access.space=.global ∧
    (if access.data.store then
       ∃ f, (f=Field.x ∨ f=Field.r ∨ f=Field.z) ∧ access.data.pc=storePC f ∧ access.data.address=a.slot f thread
     else (access.data.pc=9 ∧ access.data.address=a.base.toNat+a.alpha.toNat) ∨
       ∃ f, f≠Field.z ∧ access.data.pc=readPC f ∧ access.data.address=a.slot f thread) :=
  a.access_shape (accesses (Flow.Parallel.project run thread) (address_initial rfl) (Flow.Parallel.word_member.mpr member))

theorem Arena.parallel_index
    (run : Flow.Parallel.Runs a.context a.program (fun i => a.start memory (regs i)) words indices t)
    (member : (thread,access)∈indices) :
    access.pc=45 ∧ access.address=a.base.toNat+a.boundary.toNat+thread.val*4 := by
  have shape := index_accesses (Flow.Parallel.project run thread) (address_initial rfl) (Flow.Parallel.index_member.mpr member)
  rw [show (a.context thread).arena=a.base from rfl,a.boundary_address] at shape
  exact shape

end PtxTorchLean.Poisson.PTX.UpdateXRZ

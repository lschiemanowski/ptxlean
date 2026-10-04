import PoissonPTX.InitializeArena
import PoissonPTX.ObservedPublication

namespace PtxTorchLean.Poisson.PTX.Initialize
open Concurrent
variable {n : Nat} {a : Arena n} {memory : Memory} {i : Fin n} {s t : Flow.State}
  {access : Option Access} {index : Option IndexSources.Access}

/-- Initialization writes only output arrays. Its actual local stores preserve every
input word and the four boundary-mask bytes. -/
def Arena.Inputs (a : Arena n) (memory : Memory) (i : Fin n) (s : Flow.State) : Prop :=
  (∀ f, f=Field.input ∨ f=Field.diagonal → read64 s.core.global (a.slot f i)=read64 memory (a.slot f i)) ∧
  read32 s.core.global (a.base.toNat+a.boundary.toNat+i.val*4)=read32 memory (a.base.toNat+a.boundary.toNat+i.val*4)

theorem Arena.inputs_initial (a : Arena n) (memory : Memory) (regs : Registers) (i : Fin n) :
    a.Inputs memory i (a.start memory regs) := ⟨by intros; rfl,rfl⟩

theorem Arena.inputs_step
    (step : Flow.Observed.Step (a.context i) a.program s t access index)
    (addresses : AddressReady (a.context i) a.boundary (a.vector .input) (a.vector .rhs) (a.vector .r) (a.vector .diagonal)
      (a.vector .z) (a.vector .p) (a.vector .x) s)
    (inputs : a.Inputs memory i s) : a.Inputs memory i t := by
  have global := Flow.Observed.step_memory step
  cases access with
  | none => simpa only [Arena.Inputs,global,Flow.Observed.applyAccess] using inputs
  | some observed =>
    have shape := a.access_shape (access_step step addresses)
    by_cases store : observed.data.store=true
    · simp only [store,↓reduceIte] at shape
      obtain ⟨f,kind,address⟩ := shape.2
      have mem : t.core.global=write64 s.core.global (a.slot f i) observed.data.value := by
        simpa only [Flow.Observed.applyAccess,shape.1,store,and_self,↓reduceIte,address] using global
      constructor
      · intro g input
        have different : f≠g := by rcases kind with rfl|rfl|rfl|rfl|rfl <;> rcases input with rfl|rfl <;> decide
        rw [mem,read64_write64_disjoint _ _ _ _ (a.owners f g i i (Or.inl different))]
        exact inputs.1 g input
      · rw [mem,read32_write64_disjoint _ _ _ _ (a.boundary_disjoint f i i)]
        exact inputs.2
    · have mem : t.core.global=s.core.global := by
        simpa only [Flow.Observed.applyAccess,store,Bool.false_eq_true,and_false,↓reduceIte] using global
      simpa only [Arena.Inputs,mem] using inputs

end PtxTorchLean.Poisson.PTX.Initialize

import PoissonPTX.UpdateXRZFootprint
import PoissonPTX.ObservedTemporalReplay
import PoissonPTX.ObservedPublication

namespace PtxTorchLean.Poisson.PTX.UpdateXRZ
open Concurrent
variable {n : Nat} {a : Arena n} {memory : Memory} {i : Fin n} {s t : Flow.State}
  {access : Option Access} {index : Option IndexSources.Access}

/-- Keep only input words whose actual load instruction has not yet passed.
This permits earlier in-place stores while proving subsequent initial reads. -/
def Arena.Pending (a : Arena n) (memory : Memory) (i : Fin n) (s : Flow.State) : Prop :=
  (∀ f, f≠Field.z → s.core.pc≤readPC f → read64 s.core.global (a.slot f i)=read64 memory (a.slot f i)) ∧
  (s.core.pc≤9 → read64 s.core.global (a.base.toNat+a.alpha.toNat)=read64 memory (a.base.toNat+a.alpha.toNat)) ∧
  (s.core.pc≤45 → read32 s.core.global (a.base.toNat+a.boundary.toNat+i.val*4)=read32 memory (a.base.toNat+a.boundary.toNat+i.val*4))

theorem Arena.pending_initial (a : Arena n) (memory : Memory) (regs : Registers) (i : Fin n) :
    a.Pending memory i (a.start memory regs) := ⟨by intros; rfl,by intros; rfl,by intros; rfl⟩

theorem Arena.pending_advance (pending : a.Pending memory i s) (pc : s.core.pc≤t.core.pc)
    (mem : t.core.global=s.core.global) : a.Pending memory i t := by
  refine ⟨?_,?_,?_⟩
  · intro f notZ future; rw [mem]; exact pending.1 f notZ (by omega)
  · intro future; rw [mem]; exact pending.2.1 (by omega)
  · intro future; rw [mem]; exact pending.2.2 (by omega)

theorem Arena.pending_step
    (step : Flow.Observed.Step (a.context i) a.program s t access index)
    (addresses : AddressReady (a.context i) a.alpha (a.vector .p) (a.vector .x) (a.vector .ap)
      (a.vector .r) (a.vector .diagonal) a.boundary (a.vector .z) s)
    (pending : a.Pending memory i s) : a.Pending memory i t := by
  have global := Flow.Observed.step_memory step
  have one := step
  obtain ⟨_,op,fetch,effect⟩ := one
  have pc := Flow.Observed.eval_linear_pc effect (entry_linear op (List.mem_of_getElem? fetch))
  cases access with
  | none => exact a.pending_advance pending (by omega) global
  | some observed =>
    have shape := a.access_shape (access_step step addresses)
    by_cases store : observed.data.store=true
    · simp only [store,↓reduceIte] at shape
      obtain ⟨f,kind,position,address⟩ := shape.2
      have current := (NativeFlow.eval_access_pc effect).1
      have mem : t.core.global=write64 s.core.global (a.slot f i) observed.data.value := by
        simpa only [Flow.Observed.applyAccess,shape.1,store,and_self,↓reduceIte,address] using global
      refine ⟨?_,?_,?_⟩
      · intro g notZ future
        have different : f≠g := by
          intro same; subst g
          cases f <;> simp_all [readPC,storePC] <;> omega
        rw [mem,read64_write64_disjoint _ _ _ _ (a.owners f g i i (Or.inl different))]
        exact pending.1 g notZ (by omega)
      · intro future
        rw [mem,read64_write64_disjoint _ _ _ _ (a.alpha_disjoint f i)]
        exact pending.2.1 (by omega)
      · intro future
        rw [mem,read32_write64_disjoint _ _ _ _ (a.boundary_disjoint f i i)]
        exact pending.2.2 (by omega)
    · apply a.pending_advance pending (by omega)
      simpa only [Flow.Observed.applyAccess,store,Bool.false_eq_true,and_false,↓reduceIte] using global

end PtxTorchLean.Poisson.PTX.UpdateXRZ

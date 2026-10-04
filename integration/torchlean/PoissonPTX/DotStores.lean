import PoissonPTX.DotAddressTail
import PoissonPTX.DotStoreSyntax
import PoissonPTX.NativeFlowOrigins

namespace PtxTorchLean.Poisson.PTX.Concurrent.Dot

/-- Every actual global write uses the output field, derived from its fetched
address instructions. No assumption about the word being written is needed. -/
theorem stores_output
    (run : NativeFlow.Runs cfg ctx (program count left right output scratch) s events indices t)
    (aligned : Aligned s.core) (entry : ∀ owner, (s.core.lanes owner).pc=0)
    (member : Event.data owner access∈events) (store : access.data.store=true)
    (global : access.space=.global) :
    access.data.pc=102 ∧ access.data.address=((ctx owner).arena+output).toNat := by
  obtain ⟨before,earlier,earlierIndices,selected,out,earlierRun,one,observed⟩ :=
    NativeFlow.access_prefix run member
  obtain ⟨same,i,next,index,fetch,effect⟩ := NativeFlow.step_access_origin one observed
  subst selected
  obtain ⟨sp,addr,src,opcode,shape⟩ := Flow.Observed.store_shape effect store
  subst access
  simp only at global
  subst sp
  rw [opcode] at fetch
  obtain ⟨position,address,source⟩ := global_store_site fetch
  have ready := run_addresses earlierRun aligned entry owner
  have prepared := ready.2.2.2 position
  exact ⟨position,by simp only [address,Operand.eval,NativeFlow.lane] at prepared ⊢; rw [prepared]⟩

/-- An input word disjoint from the output field is read-only in this actual
whole-kernel history. Shared publications occupy a distinct address space. -/
theorem readonly_input {address : Nat}
    (run : NativeFlow.Runs cfg ctx (program count left right output scratch) s events indices t)
    (aligned : Aligned s.core) (entry : ∀ owner, (s.core.lanes owner).pc=0)
    (apart : ∀ owner, ((ctx owner).arena+output).toNat+8≤address ∨
      address+8≤((ctx owner).arena+output).toNat) :
    Visibility.ReadOnly events .global address := by
  intro w owner access found store global j k
  have located := (stores_output run aligned entry (List.mem_of_getElem? found) store global).2
  have separated := apart owner
  have := j.isLt
  have := k.isLt
  omega

end PtxTorchLean.Poisson.PTX.Concurrent.Dot

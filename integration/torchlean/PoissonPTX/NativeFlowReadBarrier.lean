import PoissonPTX.NativeFlowEventPrefix
import PoissonPTX.NativeFlowBarrier

namespace PtxTorchLean.Poisson.PTX.Concurrent.NativeFlow

/-- An indexed later access has an earlier actual completion at this barrier. -/
theorem access_after_barrier_index {start : State n} {events : List (Event n)} {r : Nat}
    (run : Runs cfg ctx program start events indices final) (aligned : Aligned start.core)
    (barrier : program[boundary]?=some (.sync 0)) (stops : StopsAt program boundary)
    (initial : ∀ t, (start.core.lanes t).pc≤boundary)
    (observed : events[r]?=some (Event.data reader access)) (later : boundary<access.data.pc) :
    ∃ c key, c<r ∧ events[c]?=some (.barrier (.completion key)) ∧ key.site=boundary := by
  obtain ⟨before,earlier,earlierIndices,selected,out,suffix,suffixIndices,j,hp,hs,hm,ht,he,hi⟩ := event_prefix run observed
  have mem := List.mem_of_getElem? hm
  obtain ⟨eq,op,next,index,fetch,hd⟩ := step_access_origin hs mem
  subst reader
  have pc := (eval_access_pc hd).1
  change access.data.pc=(before.core.lanes selected).pc at pc
  obtain ⟨key,hkey,site⟩ := crossed_barrier hp aligned barrier stops (initial selected) (by omega)
  obtain ⟨c,hc,hce⟩ := List.mem_iff_getElem.mp hkey
  refine ⟨c,key,by omega,?_,site⟩
  rw [he]
  simp [List.getElem?_append,hc,hce]


end PtxTorchLean.Poisson.PTX.Concurrent.NativeFlow

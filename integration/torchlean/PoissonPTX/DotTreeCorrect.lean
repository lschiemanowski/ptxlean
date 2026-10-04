import PoissonPTX.DotNumerics
import PoissonPTX.DotPublicationValue

namespace PtxTorchLean.Poisson.PTX.Concurrent.Dot.Numeric
open Visibility.Repeated

variable {cfg : Config 256} {ctx : Fin 256 → Kernel.Context}
  {start final : NativeFlow.State 256} {events : List (Event 256)} {w : Nat}
  {thread : Fin 256} {access : Access}

theorem store_properties
    (run : NativeFlow.Runs cfg ctx (program count left right output scratch) start events indices final)
    (observed : events[w]?=some (.data thread access)) (phase : Fin 9)
    (atSite : access.data.pc=storeSite phase) : access.data.store=true ∧ access.space=.shared := by
  obtain ⟨before,earlier,earlierIndices,selected,out,prior,step,member⟩ := NativeFlow.access_prefix run (List.mem_of_getElem? observed)
  obtain ⟨same,i,next,index,fetch,effect⟩ := NativeFlow.step_access_origin step member
  subst selected
  have pc := (NativeFlow.eval_access_pc effect).1.symm.trans atSite
  change (before.core.lanes thread).pc=storeSite phase at pc
  rw [pc,store_fetch] at fetch
  cases fetch
  cases effect with
  | data step => cases step with
    | data step => cases step with
      | store valid => exact ⟨rfl,rfl⟩

/-- This compositional tree lemma accepts initial publications as a boundary
contract. The full-entry theorem below derives that contract from input loads. -/
theorem tree_publication_values
    (run : NativeFlow.Runs cfg ctx (program count left right output scratch) start events indices final)
    (reset : start.core.barrier=Ptx.Barrier.reset generation)
    (entry : ∀ thread, (start.core.lanes thread).pc=0)
    (laneMap : ∀ thread, (ctx thread).lane.toNat=thread.val)
    (noWrap : scratch.toNat+2048≤2^64)
    (compatible : Visibility.Compatible initial events source) (ordered : OrderedSources events source)
    (initialValues : ∀ (w : Nat) (thread : Fin 256) (access : Access), events[w]?=some (.data thread access) →
      access.data.pc=22 → decode access.data.value=input thread.val)
    (phase : Fin 9) (observed : events[w]?=some (.data thread access))
    (pc : access.data.pc=storeSite phase) : decode access.data.value=values input phase.val thread.val := by
  have aligned : Aligned start.core := by intro t h; simp [reset,Ptx.Barrier.reset] at h
  have all : ∀ (p : Nat) (bound : p<9) (w : Nat) (thread : Fin 256) (access : Access),
      events[w]?=some (.data thread access) → access.data.pc=storeSite ⟨p,bound⟩ →
      decode access.data.value=values input p thread.val := by
    intro p
    induction p with
    | zero =>
      intro bound w thread access found atSite
      exact initialValues w thread access found atSite
    | succ p ih =>
      intro bound w thread access found atSite
      let phase : Fin 8 := ⟨p,by omega⟩
      have reads : Values.Reads (loads input phase) events := by
        intro reader ra member read f known
        obtain ⟨r,hr⟩ := List.mem_iff_getElem?.mp member
        unfold loads at known
        split at known
        · rename_i atRead
          cases known
          obtain ⟨writer,v,wa,ownerEq,hw,wp,ww,ws,across,value,bytes⟩ :=
            tree_read_source run reset entry laneMap noWrap compatible ordered hr phase false atRead
          rw [value,ih (by omega) v writer wa hw wp]
          simp only [readOffset,Bool.false_eq_true,ite_false,Nat.add_zero] at ownerEq
          simp only [ownerEq,phase]
        · split at known
          · rename_i atRead
            cases known
            obtain ⟨writer,v,wa,ownerEq,hw,wp,ww,ws,across,value,bytes⟩ :=
              tree_read_source run reset entry laneMap noWrap compatible ordered hr phase true atRead
            rw [value,ih (by omega) v writer wa hw wp]
            simp only [readOffset,ite_true] at ownerEq
            simp only [ownerEq,phase]
          · cases known
      have sum := stored run aligned entry reads ⟨p+1,bound⟩ (update_tag input phase) found atSite
      have props := store_properties run found ⟨p+1,bound⟩ atSite
      obtain ⟨_,stage,position,live⟩ := shared_store_ownership run aligned entry laneMap noWrap
        (List.mem_of_getElem? found) props.1 props.2
      have same : stage=⟨p+1,bound⟩ := store_sites.injective (position.symm.trans atSite)
      subst stage
      change thread.val<256 / 2^(p+1) at live
      simpa only [values,Reduction.Control.Numeric.values,Binary64.round,live,ite_true,phase,stride,Reduction.active] using sum
  exact all phase.val phase.isLt w thread access observed pc

/-- A total lane-indexed view of the computed input partial sums. Values outside
the launch range are unused by the reduction. -/
def partialInputs (ctx : Fin 256 → Kernel.Context) (scratch : Word) (start : NativeFlow.State 256)
    (count : Nat) (left right : Word) (lane : Nat) : Float :=
  if within : lane<256 then DotInput.partialSum (ctx ⟨lane,within⟩) scratch (NativeFlow.lane start ⟨lane,within⟩) count left right else 0

/-- Every actual shared publication in the complete native dot entry equals its
specified rounded tree value, starting from the actual admitted input loop.
No initial partial sum, shared snapshot or read result is supplied. -/
theorem publication_value
    (run : NativeFlow.Runs cfg ctx (program count left right output scratch) start events indices final)
    (reset : start.core.barrier=Ptx.Barrier.reset generation)
    (entry : ∀ thread, (start.core.lanes thread).pc=0) (live : ∀ thread, start.halted thread=false)
    (arena : ∀ thread, (ctx thread).arena=base) (laneMap : ∀ thread, (ctx thread).lane.toNat=thread.val)
    (sameInitial : ∀ thread, (start.core.lanes thread).global=initial .global)
    (bounded : count<2^30) (apart : OutputApart count left right output)
    (arrays : ∀ thread, DotInput.Arrays (DotInput.setup (ctx thread) scratch (NativeFlow.lane start thread)).core count left right)
    (outputFits : base.toNat+output.toNat+8≤2^64) (noWrap : scratch.toNat+2048≤2^64)
    (compatible : Visibility.Compatible initial events source) (ordered : OrderedSources events source)
    (phase : Fin 9) (observed : events[w]?=some (.data thread access)) (pc : access.data.pc=storeSite phase) :
    decode access.data.value=values (partialInputs ctx scratch start count left right) phase.val thread.val := by
  apply tree_publication_values run reset entry laneMap noWrap compatible ordered ?_ phase observed pc
  intro index owner a found atStore
  have aligned : Aligned start.core := by intro t h; simp [reset,Ptx.Barrier.reset] at h
  have props := store_properties run found 0 atStore
  have value := (publication_contents run aligned entry (live owner) arena (sameInitial owner) compatible
    bounded apart (arrays owner) outputFits (List.mem_of_getElem? found) props.1 atStore).2.2
  simpa [partialInputs,owner.isLt] using value

end PtxTorchLean.Poisson.PTX.Concurrent.Dot.Numeric

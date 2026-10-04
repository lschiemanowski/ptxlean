import PoissonPTX.ObservedParallelRestrict
import PoissonPTX.ObservedParallelReplay
import PoissonPTX.ObservedParallelPadding
import PoissonPTX.ObservedPaddingUnique
import PoissonPTX.RoundedLaunch

namespace PtxTorchLean.Poisson.PTX.Flow.Parallel
open Concurrent

/-- The full launch has no records owned by padding lanes. This follows from
the actual guard and return, not from an assumption that padding is silent. -/
theorem vector_active_records {ctx : Fin m → Kernel.Context} {start final : Fin m → State}
    (run : Runs ctx (VectorFlowEntry.program count body) start words indices final)
    (pcs : ∀ t, (start t).core.pc=0) (running : ∀ t, (start t).halted=false)
    (done : ∀ t, (final t).halted=true)
    (inactive : ∀ t, n≤t.val → ¬Kernel.Residual.live (ctx t) count) :
    (∀ owner a, Event.data owner a∈words → owner.val<n) ∧
      (∀ owner a, (owner,a)∈indices → owner.val<n) := by
  have empty (t : Fin m) (padding : n≤t.val) :=
    Observed.vector_padding_unique (project run t) (pcs t) (running t) (done t) (inactive t padding)
  constructor
  · intro owner a member
    by_contra wrong
    have absent := (empty owner (by omega)).2.1
    have present := word_member.mpr member
    rw [absent] at present
    simp at present
  · intro owner a member
    by_contra wrong
    have absent := (empty owner (by omega)).2.2
    have present := index_member.mpr member
    rw [absent] at present
    simp at present

theorem recover_words (enough : n≤m) (words : List (Event m))
    (active : ∀ owner a, Event.data owner a∈words → owner.val<n)
    (noBarrier : ∀ e, Event.barrier e∉words) :
    (words.filterMap (restrictEvent n)).map (renameEvent (Fin.castLE enough))=words := by
  induction words with
  | nil => rfl
  | cons e rest ih =>
    cases e with
    | barrier event => exact False.elim (noBarrier event (by simp))
    | data owner access =>
      have live := active owner access (by simp)
      have same : (⟨owner.val,live⟩ : Fin n).castLE enough=owner := Fin.ext rfl
      have later := ih (fun owner a member => active owner a (List.mem_cons_of_mem _ member))
        (fun e member => noBarrier e (List.mem_cons_of_mem _ member))
      simpa only [List.filterMap_cons,restrictEvent,dite_eq_left live,List.map_cons,renameEvent,same] using congrArg (Event.data owner access :: ·) later

theorem recover_indices (enough : n≤m) (indices : List (Fin m × IndexSources.Access))
    (active : ∀ owner a, (owner,a)∈indices → owner.val<n) :
    (indices.filterMap (restrictIndex n)).map (fun (owner,a) => (owner.castLE enough,a))=indices := by
  induction indices with
  | nil => rfl
  | cons pair rest ih =>
    have live := active pair.1 pair.2 (by simp)
    have same : (⟨pair.1.val,live⟩ : Fin n).castLE enough=pair.1 := Fin.ext rfl
    have later := ih (fun owner a member => active owner a (List.mem_cons_of_mem _ member))
    simpa only [List.filterMap_cons,restrictIndex,dite_eq_left live,List.map_cons,same] using congrArg (pair :: ·) later

end PtxTorchLean.Poisson.PTX.Flow.Parallel

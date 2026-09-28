import PtxBinary32.UnaryPointwiseReads

/-! Actual stores determine final memory. Each lane writes its own cell at one
instruction site; straight-line progress prevents a second write to that cell. -/
namespace Ptx.Scalar.ParallelUnary

private theorem scalar_store (evaluated : Scalar.eval candidate instruction s=.next next event)
    (memory : event.memory=some effect) (store : effect.kind=.store) :
    next.memory[effect.address.toNat/4]?=some effect.value := by
  cases instruction with
  | mk guard op =>
    cases op <;> cases hg : guard.eval s <;>
      simp only [Scalar.eval,hg,↓reduceIte] at evaluated
    all_goals first
      | contradiction
      | (obtain ⟨rfl,rfl⟩ := Scalar.StepResult.next.inj evaluated
         simp [Scalar.occurrence] at memory)
      | skip
    all_goals split at evaluated <;> first | contradiction | skip
    all_goals obtain ⟨rfl,rfl⟩ := Scalar.StepResult.next.inj evaluated
    all_goals simp only [Scalar.occurrence] at memory
    all_goals cases Option.some.inj memory
    all_goals first | contradiction | skip
    all_goals
      obtain ⟨inside,index⟩ := Scalar.addressIndex_ok_iff.mp (by assumption)
      rw [←index]
      apply List.getElem?_set_self
      simpa [index] using inside.2

theorem step_stored (step : Step target program candidate selected s next event)
    (memory : event.memory=some effect) (store : effect.kind=.store) :
    next.global[effect.address.toNat/4]?=some effect.value := by
  obtain ⟨_,_,i,_,exec⟩ := step
  cases exec with
  | scalarNext eval => exact scalar_store eval memory store
  | scalarHalted eval => simp [Event.memory,(Scalar.eval_halted eval).2] at memory
  | binary _ | exponential _ | reciprocal _ => simp [Event.memory] at memory

/-- A write is still visible at completion if this trace has no second write
at its address. This is a machine-state theorem, separate from graph admission. -/
theorem runs_stored (run : Runs target program s events final)
    (member : event∈events) (memory : event.memory=some effect) (store : effect.kind=.store)
    (unique : ∀other∈events, ∀written, other.memory=some written → written.kind=.store →
      written.address.toNat/4=effect.address.toNat/4 → other=event)
    (nodup : events.Nodup) :
    final.global[effect.address.toNat/4]?=some effect.value := by
  induction run with
  | nil => simp at member
  | @cons candidate selected s middle head tail final step rest ih =>
    have nd := List.nodup_cons.mp nodup
    rcases List.mem_cons.mp member with equal | member
    · subst head
      rw [runs_frame rest (effect.address.toNat/4)]
      · exact step_stored step memory store
      · intro other member written emitted kind same
        have eq := unique other (List.mem_cons_of_mem _ member) written emitted kind same
        subst other
        exact nd.1 member
    · exact ih member (fun other hm => unique other (List.mem_cons_of_mem _ hm)) nd.2

end Ptx.Scalar.ParallelUnary

namespace Ptx.Scalar.UnaryPointwise
open ParallelUnary
variable {n : Nat} {events : List (ParallelUnary.Event n)}
  {event other : ParallelUnary.Event n} {s final : ParallelUnary.State n}

/-- No event can recur: every same-lane transition advances its instruction site. -/
theorem events_nodup (run : ParallelUnary.Runs target (program op) s events final) : events.Nodup := by
  apply List.nodup_iff_injective_get.mpr
  intro p q equal
  apply Fin.ext
  exact same_site_unique run (straight op) p.val q.val (events.get p) (events.get q)
    (by simp) (by simp) (congrArg Event.thread equal) (congrArg Event.pc equal)

/-- In-place ownership and one store site prohibit multiple writes to a cell. -/
theorem stores_unique (run : ParallelUnary.Runs target (program op) (initial common before seeds) events final)
    (fit : common<2^62) (separate : n≤common)
    (first : event∈events) (second : other∈events)
    (memory : event.memory=some effect) (emitted : other.memory=some written)
    (store : effect.kind=.store) (kind : written.kind=.store)
    (address : written.address.toNat/4=effect.address.toNat/4) : other=event := by
  have own := run_memory run first memory
  have own' := run_memory run second emitted
  rcases own with ⟨_,bad,_⟩|⟨_,bad,_⟩|⟨pc,_,addr⟩ <;> try {rw [store] at bad; contradiction}
  rcases own' with ⟨_,bad,_⟩|⟨_,bad,_⟩|⟨pc',_,addr'⟩ <;> try {rw [kind] at bad; contradiction}
  rw [addr,addr',pointer_index _ (by omega),pointer_index _ (by omega)] at address
  have thread : other.thread=event.thread := Fin.ext address
  obtain ⟨p,hp⟩ := List.mem_iff_getElem?.mp first
  obtain ⟨q,hq⟩ := List.mem_iff_getElem?.mp second
  have positions := same_site_unique run (straight op) q p other event hq hp thread (pc'.trans pc.symm)
  subst q
  exact Option.some.inj (hq.symm.trans hp)

theorem stored_final (run : ParallelUnary.Runs target (program op) (initial common before seeds) events final)
    (fit : common<2^62) (separate : n≤common)
    (member : event∈events) (memory : event.memory=some effect) (store : effect.kind=.store) :
    final.global[event.thread.val]?=some effect.value := by
  have own := run_memory run member memory
  rcases own with ⟨_,bad,_⟩|⟨_,bad,_⟩|⟨_,_,addr⟩ <;> try {rw [store] at bad; contradiction}
  have stored := runs_stored run member memory store
    (fun other hm written emitted kind address => stores_unique run fit separate member hm memory emitted store kind address)
    (events_nodup run)
  rw [addr,pointer_index event.thread.val (by omega)] at stored
  exact stored

end Ptx.Scalar.UnaryPointwise

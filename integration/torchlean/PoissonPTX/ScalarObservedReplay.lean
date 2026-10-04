import PoissonPTX.ScalarObservedOrder

namespace PtxTorchLean.Poisson.PTX.Scalar.Observed

/-- At every still-future read, prior stores have preserved its initial bytes. -/
def ReadFrame (initial : Space → Memory) (events : List Sources.Access) (s : Flow.State) : Prop :=
  ∀ a∈events, a.store=false → ∀ k : Fin 8, k.val<a.width.bytes →
    s.core.memory a.space (a.address+k.val)=initial a.space (a.address+k.val)

def FutureSeparate (events : List Sources.Access) : Prop :=
  ∀ w∈events, w.store=true → ∀ r∈events, r.store=false → w.space=r.space → w.pc<r.pc →
    w.address+w.width.bytes≤r.address ∨ r.address+r.width.bytes≤w.address

theorem sequence_replay (actual : Sequence ctx code s events t)
    (plain : ∀ i∈code, segment i=true) (reads : ReadValues initial events)
    (apart : FutureSeparate events) (frame : ReadFrame initial events s) : Scalar.Sequence ctx code s t := by
  induction actual with
  | nil => exact .nil
  | @cons i s middle first code rest t alive step run ih =>
    have firstMember : ∀ a∈first, a∈first++rest := fun _ mem => List.mem_append_left _ mem
    have restMember : ∀ a∈rest, a∈first++rest := fun _ mem => List.mem_append_right _ mem
    have one : Scalar.Eval ctx i s middle := replay step (by
      intro a member read k small
      exact (reads a (firstMember a member) read k small).trans (frame a (firstMember a member) read k small).symm)
    have nextFrame : ReadFrame initial rest middle := by
      intro r member read k small
      rw [eval_memory step]
      apply Eq.trans (Sources.publish_outside ?_) (frame r (restMember r member) read k small)
      intro w written store space
      have headPC : w.pc=s.core.pc := by
        rcases eval_events step with empty | ⟨a,single,position⟩
        · simp [empty] at written
        · have same : w=a := by simpa [single] using written
          subst w; exact position
      have lower := (sequence_bounds run (fun i mem => plain i (by simp [mem])) r member).1
      have next := eval_position step (plain _ (by simp))
      have separate := apart w (firstMember w written) store r (restMember r member) read space (by omega)
      omega
    exact .cons alive one (ih (fun i mem => plain i (by simp [mem]))
      (fun a mem => reads a (restMember a mem))
      (fun w mem store r seen => apart w (restMember w mem) store r (restMember r seen)) nextFrame)

/-- Source compatibility and no-future causality establish the complete
initial-byte read relation, without a premise about numerical values. -/
theorem reads_of_admission (compatible : Sources.Compatible initial events source) (admitted : Sources.NoFuture events source)
    (writers : ∀ (r : Nat) (ra : Sources.Access), events[r]?=some ra → ra.store=false →
      ∀ (w : Nat) (wa : Sources.Access), events[w]?=some wa → wa.store=true → wa.space=ra.space →
        ∀ j k : Fin 8, j.val<wa.width.bytes → k.val<ra.width.bytes → wa.address+j.val=ra.address+k.val →
          r<w ∧ wa.address=ra.address ∧ wa.width=ra.width) : ReadValues initial events := by
  intro ra member read k small
  obtain ⟨r,found⟩ := List.mem_iff_getElem?.mp member
  exact (Sources.initial_value compatible admitted found read (writers r ra found read) k small).2

theorem admitted_sequence (actual : Sequence ctx code s events t) (plain : ∀ i∈code, segment i=true)
    (compatible : Sources.Compatible s.core.memory events source) (admitted : Sources.NoFuture events source)
    (writers : ∀ (r : Nat) (ra : Sources.Access), events[r]?=some ra → ra.store=false →
      ∀ (w : Nat) (wa : Sources.Access), events[w]?=some wa → wa.store=true → wa.space=ra.space →
        ∀ j k : Fin 8, j.val<wa.width.bytes → k.val<ra.width.bytes → wa.address+j.val=ra.address+k.val →
          r<w ∧ wa.address=ra.address ∧ wa.width=ra.width)
    (apart : FutureSeparate events) : Scalar.Sequence ctx code s t :=
  sequence_replay actual plain (reads_of_admission compatible admitted writers) apart (by intro a member read k small; rfl)

end PtxTorchLean.Poisson.PTX.Scalar.Observed

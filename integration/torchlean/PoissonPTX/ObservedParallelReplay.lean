import PoissonPTX.ObservedParallel

namespace PtxTorchLean.Poisson.PTX.Flow.Parallel
variable {n : Nat} {ctx : Fin n → Kernel.Context} {s t : Fin n → State}
  {words : List (Concurrent.Event n)} {indices : List (Fin n × IndexSources.Access)}

theorem word_member : a∈wordsFor thread words ↔ Concurrent.Event.data thread a∈words := by
  simp only [wordsFor,List.mem_filterMap]
  constructor
  · rintro ⟨event,member,selected⟩
    cases event with
    | barrier => simp at selected
    | data owner observed =>
      by_cases same : owner=thread
      · simp [same] at selected
        subst observed
        simpa [same] using member
      · simp [same] at selected
  · intro member
    exact ⟨_,member,by simp⟩

theorem index_member : a∈indicesFor thread indices ↔ (thread,a)∈indices := by
  simp only [indicesFor,List.mem_filterMap]
  constructor
  · rintro ⟨⟨owner,observed⟩,member,selected⟩
    by_cases same : owner=thread
    · simp [same] at selected
      subst observed
      simpa [same] using member
    · simp [same] at selected
  · intro member; exact ⟨_,member,by simp⟩

/-- Every pair is about recorded accesses in the whole launch. This permits
all schedules while making the physical non-aliasing obligation explicit. -/
def Separate (words : List (Concurrent.Event n)) (indices : List (Fin n × IndexSources.Access)) : Prop :=
  (∀ writer w, Concurrent.Event.data writer w∈words → w.data.store=true →
    ∀ reader r, Concurrent.Event.data reader r∈words → r.data.store=false → w.space=r.space →
      w.data.address+8≤r.data.address ∨ r.data.address+8≤w.data.address) ∧
  (∀ writer w, Concurrent.Event.data writer w∈words → w.data.store=true → w.space=.global →
    ∀ reader r, (reader,r)∈indices → w.data.address+8≤r.address ∨ r.address+4≤w.data.address)

theorem values (compatible : Concurrent.Visibility.Compatible initial words wordSource)
    (indexCompatible : IndexSources.Compatible (initial .global) words indices indexSource)
    (apart : Separate words indices) (thread : Fin n) :
    (∀ a∈wordsFor thread words, a.data.store=false → a.data.value=read64 (initial a.space) a.data.address) ∧
    (∀ a∈indicesFor thread indices, a.value=read32 (initial .global) a.address) := by
  constructor
  · intro a member read
    have member := word_member.mp member
    obtain ⟨r,located⟩ := List.mem_iff_getElem?.mp member
    apply Concurrent.Visibility.read_only_value compatible located read
    intro w writer wa fetched store same j k
    have disjoint := apart.1 writer wa (List.mem_of_getElem? fetched) store thread a member read same
    have := j.isLt; have := k.isLt; omega
  · intro a member
    have member := index_member.mp member
    obtain ⟨r,located⟩ := List.mem_iff_getElem?.mp member
    apply IndexSources.read_only_value indexCompatible located
    intro w writer wa fetched store global j k
    have disjoint := apart.2 writer wa (List.mem_of_getElem? fetched) store global thread a member
    have := j.isLt; have := k.isLt; omega

/-- Derive each complete local execution from actual launch interleaving and
byte-source constraints. No local execution or desired read value is supplied. -/
theorem replay (run : Runs ctx program s words indices t)
    (compatible : Concurrent.Visibility.Compatible initial words wordSource)
    (indexCompatible : IndexSources.Compatible (initial .global) words indices indexSource)
    (apart : Separate words indices) (memory : ∀ i, (s i).core.memory=initial) (thread : Fin n) :
    Flow.Runs (ctx thread) program (s thread) (t thread) := by
  have calculated := values compatible indexCompatible apart thread
  apply Observed.replay (project run thread) calculated.1 calculated.2
  · constructor
    · intro w stored store r readmem read same
      exact apart.1 thread w (word_member.mp stored) store thread r (word_member.mp readmem) read same
    · intro w stored store global r readmem
      exact apart.2 thread w (word_member.mp stored) store global thread r (index_member.mp readmem)
  · constructor
    · intro a _ _; rw [memory thread]
    · intro a _
      have global := congrFun (memory thread) Space.global
      change (s thread).core.global=initial .global at global
      rw [global]

end PtxTorchLean.Poisson.PTX.Flow.Parallel

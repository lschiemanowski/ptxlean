import PoissonPTX.ObservedParallel
import Mathlib.Data.Finset.Basic

namespace PtxTorchLean.Poisson.PTX.Flow.Parallel
variable {n : Nat} {ctx : Fin n → Kernel.Context} {s t u : Fin n → State}

theorem append (first : Runs ctx program s wa ia t) (second : Runs ctx program t wb ib u) :
    Runs ctx program s (wa++wb) (ia++ib) u := by
  induction first with
  | nil => exact second
  | cons step rest ih => simpa only [List.append_assoc] using Runs.cons step (ih second)

/-- A returning thread can run alone while the other threads retain their
states. This constructs a legal interleaving, without a fairness assumption. -/
theorem lift (thread : Fin n)
    (run : Observed.Runs (ctx thread) program start words indices final)
    (states : Fin n → State) (atStart : states thread=start) :
    Runs ctx program states (words.map (Concurrent.Event.data thread))
      (indices.map (thread,·)) (Function.update states thread final) := by
  induction run generalizing states with
  | nil => simpa [← atStart,Function.update_eq_self] using (Runs.nil (ctx:=ctx) (program:=program) (s:=states))
  | @cons start middle access index words indices final step rest ih =>
    have one : Observed.Step (ctx thread) program (states thread) middle access index := by simpa only [atStart] using step
    have tail := ih (Function.update states thread middle) (by simp)
    have joined := Runs.cons one tail
    simpa only [List.map_append,Function.update_idem] using joined

/-- Combine a distinct finite list of threads. Record membership is retained
for source admission after the chosen interleaving is constructed. -/
theorem combine (order : List (Fin n)) (distinct : order.Nodup)
    (localWords : Fin n → List Concurrent.Access) (localIndices : Fin n → List IndexSources.Access)
    (run : ∀ i, Observed.Runs (ctx i) program (s i) (localWords i) (localIndices i) (t i)) :
    ∃ words indices final, Runs ctx program s words indices final ∧
      (∀ i∈order, final i=t i) ∧ (∀ i∉order, final i=s i) ∧
      (∀ i a, Concurrent.Event.data i a∈words → a∈localWords i) ∧
      (∀ i a, (i,a)∈indices → a∈localIndices i) := by
  induction order with
  | nil => exact ⟨[],[],s,.nil,by simp,by simp,by simp,by simp⟩
  | cons thread rest ih =>
    have nodup := List.nodup_cons.mp distinct
    obtain ⟨wa,ia,middle,first,finished,untouched,wordMembers,indexMembers⟩ := ih nodup.2
    have second := lift thread (run thread) middle (untouched thread nodup.1)
    refine ⟨_,_,_,append first second,?_,?_,?_,?_⟩
    · intro i included
      rcases List.mem_cons.mp included with same | member
      · subst i; simp
      · have different : i≠thread := by intro eq; subst i; exact nodup.1 member
        rw [Function.update_of_ne different]
        exact finished i member
    · intro i excluded
      have different : i≠thread := by intro eq; subst i; exact excluded (by simp)
      rw [Function.update_of_ne different]
      exact untouched i (by intro member; exact excluded (List.mem_cons_of_mem _ member))
    · intro i a member
      rcases List.mem_append.mp member with old | new
      · exact wordMembers i a old
      · obtain ⟨b,member,eq⟩ := List.mem_map.mp new
        cases eq
        exact member
    · intro i a member
      rcases List.mem_append.mp member with old | new
      · exact indexMembers i a old
      · obtain ⟨b,member,eq⟩ := List.mem_map.mp new
        cases eq
        exact member

/-- General joint execution existence for a finite family of returning local
executions, preserving the provenance of every recorded access. -/
theorem all_threads
    (localWords : Fin n → List Concurrent.Access) (localIndices : Fin n → List IndexSources.Access)
    (run : ∀ i, Observed.Runs (ctx i) program (s i) (localWords i) (localIndices i) (t i)) :
    ∃ words indices, Runs ctx program s words indices t ∧
      (∀ i a, Concurrent.Event.data i a∈words → a∈localWords i) ∧
      (∀ i a, (i,a)∈indices → a∈localIndices i) := by
  obtain ⟨words,indices,final,actual,finished,_,wordMembers,indexMembers⟩ :=
    combine (Finset.univ.toList) (Finset.nodup_toList _) localWords localIndices run
  have eq : final=t := by funext i; exact finished i (by simp)
  subst final
  exact ⟨words,indices,actual,wordMembers,indexMembers⟩

end PtxTorchLean.Poisson.PTX.Flow.Parallel

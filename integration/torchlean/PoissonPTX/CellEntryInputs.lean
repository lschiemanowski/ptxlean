import PoissonPTX.CellEntry

namespace PtxTorchLean.Poisson.PTX.CellEntry

theorem setup_pc (step : CellPrologue.eval ctx op s=some t) : t.core.pc=s.core.pc+1 := by
  cases op <;> simp [CellPrologue.eval] at step
  all_goals obtain ⟨_,rfl⟩ := step; rfl

theorem setup_global (step : CellPrologue.eval ctx op s=some t) : t.core.global=s.core.global := by
  cases op <;> simp [CellPrologue.eval] at step
  all_goals obtain ⟨_,rfl⟩ := step; rfl

theorem gather_member {pc : Nat} (fetch : (program width cells source)[pc]?=some (.gather op)) :
    op∈CellGather.code width cells source := by
  have member := List.mem_of_getElem? fetch
  simp only [program,List.mem_append,List.mem_map,List.mem_singleton] at member
  rcases member with ((⟨setup,_,same⟩ | wrong) | ⟨data,member,same⟩) | wrong
  · cases same
  · cases wrong
  · cases same; exact member
  · cases wrong

theorem gather_safe {pc : Nat} (fetch : (program width cells source)[pc]?=some (.gather op)) :
    Indexed.Candidate.noGlobalStore op=true ∧ Indexed.Candidate.noSharedLoad op=true := by
  have all : ∀ i∈CellGather.code width cells source,
      Indexed.Candidate.noGlobalStore i=true ∧ Indexed.Candidate.noSharedLoad i=true := by
    simp [CellGather.code,Indexed.Candidate.noGlobalStore,Indexed.Candidate.noSharedLoad]
  exact all op (gather_member fetch)

theorem gather_plain {pc : Nat} (fetch : (program width cells source)[pc]?=some (.gather op)) :
    Indexed.noFP op=true := by
  have all : ∀ i∈CellGather.code width cells source, Indexed.noFP i=true := by
    simp [CellGather.code,Indexed.noFP,PTX.noFP]
  exact all op (gather_member fetch)

variable {n : Nat} {s t : State n} {cfg : Concurrent.Config n}
  {ctx : Fin n → CellPrologue.Context} {out : Outcome n}

theorem step_no_global_store (step : Step cfg ctx (program width cells source) thread s out)
    (member : Concurrent.Event.data writer access∈out.events) (store : access.data.store=true) :
    access.space≠.global := by
  obtain ⟨fresh,i,fetch,dispatch⟩ := step
  cases dispatch with
  | setup => simp at member
  | skip => simp at member
  | gather hd =>
    have same : ‹Option Concurrent.Access›=some access ∧ thread=writer := by simpa using member
    have shared := Indexed.Candidate.store_shared (same.1 ▸ hd) (gather_safe fetch).1 store
    simp [shared]
  | sync =>
    simp only [synchronize,Concurrent.synchronize] at member
    split at member <;> simp_all

theorem no_global_store (run : Runs cfg ctx (program width cells source) s events indices t)
    (member : Concurrent.Event.data writer access∈events) (store : access.data.store=true) :
    access.space≠.global := by
  induction run with
  | nil => simp at member
  | cons step _ ih =>
    rcases List.mem_append.mp member with first | later
    · exact step_no_global_store step first store
    · exact ih later

theorem step_global (step : Step cfg ctx (program width cells source) selected s out) (thread : Fin n) :
    (out.state.core.lanes thread).global=(s.core.lanes thread).global := by
  obtain ⟨fresh,i,fetch,dispatch⟩ := step
  cases dispatch with
  | setup he =>
    by_cases same : thread=selected
    · subst thread; simpa [setLane,Concurrent.setLane,lane] using setup_global he
    · simp [setLane,Concurrent.setLane,Function.update,same]
  | gather he =>
    by_cases same : thread=selected
    · subst thread; simpa [Concurrent.setLane] using Indexed.Candidate.data_global he (gather_safe fetch).1
    · simp [Concurrent.setLane,Function.update,same]
  | skip =>
    by_cases same : thread=selected <;> simp [Concurrent.setLane,Function.update,same]
  | sync =>
    simp only [synchronize,Concurrent.synchronize]
    split <;> rfl

theorem runs_global (run : Runs cfg ctx (program width cells source) s events indices t) (thread : Fin n) :
    (t.core.lanes thread).global=(s.core.lanes thread).global := by
  induction run with
  | nil => rfl
  | cons step _ ih => exact ih.trans (step_global step thread)

/-- Four-byte sources are forced to initialization by the actual instruction
history, not by a supplied read value or assumed list of missing writes. -/
theorem index_value {r : Nat} {access : IndexSources.Access} (run : Runs cfg ctx (program width cells source) s events indices t)
    (compatible : IndexSources.Compatible initial events indices chosen)
    (observed : indices[r]?=some (thread,access)) : access.value=read32 initial access.address := by
  apply IndexSources.read_only_value compatible observed
  apply IndexSources.readonly_of_no_global_stores
  intro w writer wa observed store
  exact no_global_store run (List.mem_of_getElem? observed) store

/-- The same absence of global stores fixes every eight-byte global read. -/
theorem word_value {r : Nat} {access : Concurrent.Access} (run : Runs cfg ctx (program width cells source) s events indices t)
    (compatible : Concurrent.Visibility.Compatible initial events chosen)
    (observed : events[r]?=some (.data thread access))
    (read : access.data.store=false) (global : access.space=.global) :
    access.data.value=read64 (initial .global) access.data.address := by
  rw [← global]
  apply Concurrent.Visibility.read_only_value compatible observed read
  intro w writer wa observed store space
  exact False.elim (no_global_store run (List.mem_of_getElem? observed) store (space.trans global))

end PtxTorchLean.Poisson.PTX.CellEntry

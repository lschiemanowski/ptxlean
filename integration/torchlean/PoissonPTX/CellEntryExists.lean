import PoissonPTX.CellEntryWave
import PoissonPTX.CellEntryResult

namespace PtxTorchLean.Poisson.PTX.CellEntry

theorem step_read_global (step : Step cfg ctx (program width cells source) selected s out)
    (member : Concurrent.Event.data owner a∈out.events) (read : a.data.store=false) : a.space=.global := by
  obtain ⟨fresh,i,fetch,dispatch⟩ := step
  cases dispatch with
  | setup => simp at member
  | skip => simp at member
  | gather actual =>
    have same : ‹Option Concurrent.Access›=some a ∧ selected=owner := by simpa using member
    exact Indexed.Candidate.load_global (same.1 ▸ actual) (gather_safe fetch).2 read
  | sync =>
    simp only [synchronize,Concurrent.synchronize] at member
    split at member <;> simp_all

theorem read_global (run : Runs cfg ctx (program width cells source) s events indices final)
    (member : Concurrent.Event.data owner a∈events) (read : a.data.store=false) : a.space=.global := by
  induction run with
  | nil => simp at member
  | cons step rest ih =>
    rcases List.mem_append.mp member with first | later
    · exact step_read_global step first read
    · exact ih later

theorem initial_sources (run : Runs cfg ctx (program width cells source) s events indices final)
    (words : Words (memory .global) events) (ix : Indices (memory .global) indices) :
    Concurrent.Visibility.Compatible memory events (fun _ _ => .initial) ∧
      Concurrent.Visibility.Performed events (fun _ _ => .initial) ∧
      IndexSources.Compatible (memory .global) events indices (fun _ _ => .initial) := by
  refine ⟨?_,?_,?_⟩
  · intro r reader a found read k
    have member := List.mem_of_getElem? found
    have global := read_global run member read
    change byte a.data.value k.val=memory a.space (a.data.address+k.val)
    rw [words reader a member read global,global]
    exact Sources.byte_read64 _ _ k
  · intro w r writer reader wa ra hw hr write read sw sr across j k equal
    have global := read_global run (List.mem_of_getElem? hr) read
    rw [global] at sr; cases sr
  · intro r reader a found k
    change IndexSources.byte32 a.value k.val=memory .global (a.address+k.val)
    rw [ix reader a (List.mem_of_getElem? found)]
    exact IndexSources.byte_read32 _ _ k

/-- A complete admitted prefix exists for arbitrary valid input bytes. Every
lane reaches the next instruction after the real collective release, and its
state agrees with the independently proved local gather computation. -/
theorem admitted_prefix_exists (cfg : Concurrent.Config n) (ctx : Fin n → CellPrologue.Context) (start : State n)
    (pcs : ∀ u, (start.core.lanes u).pc=0)
    (reset : start.core.barrier=Ptx.Barrier.reset generation) (site : start.core.site=none)
    (initial : ∀ u, (start.core.lanes u).global=memory .global)
    (positive : 0<width) (fits : width*width<2^32)
    (valid : ∀ u, (ctx u).lane.toNat<width*width →
      CellGather.Valid (Local.beforeGather (ctx u) width (lane start u)) width cells source) :
    ∃ final events indices,
      Runs cfg ctx (program width cells source) start events indices final ∧
      (∀ u, (final.core.lanes u).pc=21) ∧
      final.core.barrier=Ptx.Barrier.reset (generation+1) ∧ final.core.site=none ∧
      Concurrent.Visibility.Compatible memory events (fun _ _ => .initial) ∧
      Concurrent.Visibility.Performed events (fun _ _ => .initial) ∧
      IndexSources.Compatible (memory .global) events indices (fun _ _ => .initial) ∧
      ∀ u, lane final u=Local.finish (ctx u) width cells source (lane start u) := by
  obtain ⟨final,events,indices,run,done,next,empty,words,ix⟩ :=
    prefix_exists cfg ctx start pcs reset site initial positive fits valid
  obtain ⟨compatible,performed,indexCompatible⟩ := initial_sources run words ix
  refine ⟨final,events,indices,run,done,next,empty,compatible,performed,indexCompatible,?_⟩
  intro u
  apply completed_lane run ?_ initial compatible indexCompatible u (pcs u) (done u) positive fits (valid u)
  intro v waiting
  simp [reset,Ptx.Barrier.reset] at waiting

end PtxTorchLean.Poisson.PTX.CellEntry

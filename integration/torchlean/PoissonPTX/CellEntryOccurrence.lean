import PoissonPTX.CellEntryStores
import PoissonPTX.CellEntryStorePath
import PoissonPTX.CellEntryReplay

namespace PtxTorchLean.Poisson.PTX.CellEntry
open Ptx

def Wrote (events : List (Concurrent.Event n)) (owner : Fin n) : Prop :=
  ∃ a, Concurrent.Event.data owner a∈events ∧ a.data.store=true ∧ a.space=.shared

variable {n : Nat} {s t : State n} {out : Outcome n} {cfg : Concurrent.Config n}
  {ctx : Fin n → CellPrologue.Context}

theorem store_fetch : (program width cells source)[19]?=
    some (.gather (.data (.store64 .shared (.offset 2 0) (.reg 11)))) := by
  simp [program,CellPrologue.program,CellGather.code]

/-- A lane at its store cannot advance unless the actual record is emitted.
Another lane's barrier request cannot move it past the missing store. -/
theorem missing_stutters (step : Step cfg ctx (program width cells source) selected s out)
    (aligned : Concurrent.Aligned s.core) (owner : Fin n) (pc : (s.core.lanes owner).pc=19)
    (absent : ¬Wrote out.events owner) : lane out.state owner=lane s owner := by
  obtain ⟨fresh,i,fetch,dispatch⟩ := step
  cases dispatch with
  | setup =>
    by_cases same : owner=selected
    · subst owner; rw [pc,store_fetch] at fetch; cases fetch
    · simp [lane,setLane,Concurrent.setLane,Function.update,same]
  | skip =>
    by_cases same : owner=selected
    · subst owner; rw [pc,store_fetch] at fetch; cases fetch
    · simp [lane,Concurrent.setLane,Function.update,same]
  | gather hd =>
    by_cases same : owner=selected
    · subst owner
      rw [pc,store_fetch] at fetch
      cases fetch
      cases hd with
      | data he => cases he with
        | ordinary plain _ => simp [Concurrent.ordinary] at plain
        | store _ =>
          exfalso
          apply absent
          exact ⟨⟨.shared,⟨(s.core.lanes selected).pc,true,
            (Operand.eval (s.core.lanes selected) (.offset 2 0)).toNat,
            Operand.eval (s.core.lanes selected) (.reg 11)⟩⟩,by simp,rfl,rfl⟩
    · simp [lane,Concurrent.setLane,Function.update,same]
  | sync =>
    let c := Concurrent.barrierConfig cfg s.core selected
    let r := Concurrent.barrierRequest cfg s.core selected 0
    generalize hr : Barrier.step c s.core.barrier r=result
    cases disposition : result.disposition with
    | rejectedWrongKey =>
      simp [lane,synchronize,Concurrent.synchronize,← show c=Concurrent.barrierConfig cfg s.core selected from rfl,
        ← show r=Concurrent.barrierRequest cfg s.core selected 0 from rfl,hr,disposition]
    | waiting =>
      simp [lane,synchronize,Concurrent.synchronize,← show c=Concurrent.barrierConfig cfg s.core selected from rfl,
        ← show r=Concurrent.barrierRequest cfg s.core selected 0 from rfl,hr,disposition]
    | released =>
      have pcs := Concurrent.release_aligned cfg s.core selected 0 aligned
        (by change (Barrier.step c s.core.barrier r).disposition=_; rw [hr,disposition])
      have here := (pcs owner).symm.trans pc
      rw [here,store_fetch] at fetch
      cases fetch

theorem local_store_not_self (step : Local.Step context (program width cells source) x x)
    (pc : x.core.pc=19) : False := by
  obtain ⟨i,fetch,he⟩ := step
  rw [pc,store_fetch] at fetch
  cases fetch
  simp only [Local.eval,Indexed.eval,PTX.eval] at he
  split at he
  · simp only [Option.map_some,Option.some.injEq] at he
    have same := congrArg (fun q => q.core.pc) he
    change x.core.pc+1=x.core.pc at same
    omega
  · simp at he

theorem avoid_missing (run : Runs cfg ctx (program width cells source) s events indices t)
    (aligned : Concurrent.Aligned s.core) (initial : ∀ u, (s.core.lanes u).global=memory)
    (words : Words memory events) (indexValues : Indices memory indices)
    (owner : Fin n) (absent : ¬Wrote events owner) :
    Local.Avoid (ctx owner) (program width cells source) 19 (lane s owner) (lane t owner) := by
  induction run with
  | nil => exact .nil
  | @cons selected s out rest indices final step tail ih =>
    have firstAbsent : ¬Wrote out.events owner := by
      rintro ⟨a,member,store,shared⟩
      exact absent ⟨a,List.mem_append_left _ member,store,shared⟩
    have laterAbsent : ¬Wrote rest owner := by
      rintro ⟨a,member,store,shared⟩
      exact absent ⟨a,List.mem_append_right _ member,store,shared⟩
    have later := ih (step_aligned step aligned) (fun u => (step_global step u).trans (initial u))
      (fun u a member read global => words u a (List.mem_append_right _ member) read global)
      (fun u a member => indexValues u a (List.mem_append_right _ member)) laterAbsent
    rcases step_local step aligned initial
      (fun u a member read global => words u a (List.mem_append_left _ member) read global)
      (fun u a member => indexValues u a (List.mem_append_left _ member)) owner with equal | one
    · rw [equal]; exact later
    · apply Local.Avoid.cons one ?_ later
      intro pc
      have same := missing_stutters step aligned owner pc firstAbsent
      rw [same] at one
      exact local_store_not_self one pc

/-- Each completed active lane really emitted its store, independent of the
old shared bytes. Source constraints justify the trace, not store coverage. -/
theorem completed_wrote (run : Runs cfg ctx (program width cells source) s events indices t)
    (aligned : Concurrent.Aligned s.core) (initial : ∀ u, (s.core.lanes u).global=memory .global)
    (words : Concurrent.Visibility.Compatible memory events chosen)
    (indexSources : IndexSources.Compatible (memory .global) events indices selected)
    (owner : Fin n) (pc : (s.core.lanes owner).pc=0) (done : (t.core.lanes owner).pc=21)
    (positive : 0<width) (fits : width*width<2^32) (active : (ctx owner).lane.toNat<width*width)
    (valid : CellGather.Valid (Local.beforeGather (ctx owner) width (lane s owner)) width cells source) :
    Wrote events owner := by
  classical
  by_contra absent
  obtain ⟨mid,first,atStore⟩ := Local.reaches_store (ctx owner) (lane s owner) pc positive fits active valid
  apply Local.cannot_avoid first atStore (by rw [store_fetch]; simp)
    (avoid_missing run aligned initial ?_ ?_ owner absent)
  · simp [lane,done,program_length]
  · intro u a member read global
    obtain ⟨r,observed⟩ := List.mem_iff_getElem?.mp member
    exact word_value run words observed read global
  · intro u a member
    obtain ⟨r,observed⟩ := List.mem_iff_getElem?.mp member
    exact index_value run indexSources observed

end PtxTorchLean.Poisson.PTX.CellEntry

import PoissonPTX.NativeFlowAccessOrder
import PoissonPTX.ConcurrentValues

namespace PtxTorchLean.Poisson.PTX.Concurrent.NativeFlow.Numeric
open Concurrent.Values

def transfer (loads : Nat → Option (Fin n → Float)) (pc : Nat) (table : Table n) : NativeFlow.Instr → Table n
  | .flow (.data (.data op)) => Values.transfer loads pc table (.data op)
  | _ => empty

def tag (program : List NativeFlow.Instr) (loads : Nat → Option (Fin n → Float)) : Nat → Table n
  | 0 => empty
  | pc+1 => match program[pc]? with
    | some i => transfer loads pc (tag program loads pc) i
    | none => empty

/-- Taken control transfers enter a conservative table with no register facts.
This allows actual prefix loops without assuming a straight-line execution. -/
def Entries (program : List NativeFlow.Instr) (loads : Nat → Option (Fin n → Float)) : Prop :=
  ∀ (pc : Nat) (i : Flow.Instr), program[pc]?=some (.flow i) →
    targets (fun target => ∀ thread s, Ready (tag program loads target) thread s) i

def Invariant (program : List NativeFlow.Instr) (loads : Nat → Option (Fin n → Float))
    (s : NativeFlow.State n) : Prop := ∀ thread, Ready (tag program loads (s.core.lanes thread).pc) thread (s.core.lanes thread)

theorem flow_ready
    (actual : Flow.Observed.Eval ctx i s t access index)
    (fetch : program[s.core.pc]?=some (.flow i))
    (ready : Ready (tag program loads s.core.pc) thread s.core)
    (entries : Entries program loads)
    (reads : ∀ a, access=some a → a.data.store=false → ∀ f, loads a.data.pc=some f → decode a.data.value=f thread) :
    Ready (tag program loads t.core.pc) thread t.core := by
  cases actual with
  | data step =>
    have counter := Indexed.Candidate.data_pc step
    rw [counter,tag,fetch]
    cases step with
    | data step =>
      apply Values.data_ready step ready
      intro a equal read f known
      have pc := Concurrent.access_pc (equal ▸ step)
      exact reads a equal read f (pc ▸ known)
    | mad32 => exact empty_ready
    | wide4 => exact empty_ready
    | load32 => exact empty_ready
  | simple ordinary =>
    have destination := entries _ _ fetch
    cases i <;> simp only [Flow.simple,Flow.next,Flow.goto,Flow.halt]
    · exact False.elim (ordinary _ rfl)
    · change Ready (tag program loads (s.core.pc+1)) thread _
      rw [tag,fetch]; exact empty_ready
    · change Ready (tag program loads (s.core.pc+1)) thread _
      rw [tag,fetch]; exact empty_ready
    · split
      · exact destination _ _
      · change Ready (tag program loads (s.core.pc+1)) thread _
        rw [tag,fetch]; exact empty_ready
    · exact destination _ _
    · split
      all_goals change Ready (tag program loads (s.core.pc+1)) thread _
      all_goals rw [tag,fetch]; exact empty_ready
    · split
      all_goals change Ready (tag program loads (s.core.pc+1)) thread _
      all_goals rw [tag,fetch]; exact empty_ready
    · change Ready (tag program loads (s.core.pc+1)) thread _
      rw [tag,fetch]; exact empty_ready

theorem step_invariant {s : NativeFlow.State n}
    (actual : NativeFlow.Step cfg ctx program selected s out) (aligned : Aligned s.core)
    (inv : Invariant program loads s) (entries : Entries program loads)
    (reads : Reads loads out.events) : Invariant program loads out.state := by
  cases actual with
  | @flow instruction _ next access index running fresh fetch effect =>
    intro owner
    by_cases same : owner=selected
    · subst owner
      simp only [update,setLane,Function.update_self]
      apply flow_ready effect fetch (inv selected) entries
      intro a equal read f known
      exact reads selected a (by simp [equal]) read f known
    · simpa only [update,setLane,Function.update_of_ne same] using inv owner
  | @sync _ resource running fresh fetch =>
    intro owner
    simp only [synchronize]
    split
    · exact inv owner
    · exact inv owner
    · rename_i released
      have same := release_aligned cfg s.core selected resource aligned released owner
      change Ready (tag program loads ((s.core.lanes owner).pc+1)) owner _
      rw [same,tag,fetch]; exact empty_ready

theorem runs_invariant
    (actual : NativeFlow.Runs cfg ctx program start events indices final) (aligned : Aligned start.core)
    (inv : Invariant program loads start) (entries : Entries program loads)
    (reads : Reads loads events) : Invariant program loads final := by
  induction actual with
  | nil => exact inv
  | cons step rest ih =>
    exact ih (NativeFlow.step_aligned step aligned)
      (step_invariant step aligned inv entries (fun t a h => reads t a (List.mem_append_left _ h)))
      (fun t a h => reads t a (List.mem_append_right _ h))

end PtxTorchLean.Poisson.PTX.Concurrent.NativeFlow.Numeric

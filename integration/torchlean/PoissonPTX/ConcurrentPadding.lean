import PoissonPTX.ConcurrentOwnership

namespace PtxTorchLean.Poisson.PTX.Concurrent.Padding
open Ptx

/-- Guard, barrier and end positions are outside the arithmetic bodies. -/
def outside (program : List Instr) (pc : Nat) : Bool :=
  match program[pc]? with
  | some (.data _) => false
  | _ => true

/-- Branches use the fixed active-lane count and send padding to boundaries;
a released barrier advances to another boundary rather than into a body. -/
def Boundaries (program : List Instr) (active : Nat) : Prop :=
  (∀ pc count target : Nat, program[pc]?=some (Instr.skip count target) →
    count=active ∧ outside program target=true) ∧
  (∀ (pc : Nat) resource, program[pc]?=some (Instr.sync resource) → outside program (pc+1)=true)

def Invariant (program : List Instr) (active : Nat) (s : State n) : Prop :=
  ∀ thread, active≤thread.val → outside program (s.lanes thread).pc=true

theorem step_invariant {s : State n} (step : Step cfg program selected s out)
    (aligned : Aligned s) (inv : Invariant program active s) (bounds : Boundaries program active) :
    Invariant program active out.state := by
  obtain ⟨fresh,i,fetch,h⟩ := step
  cases h with
  | data hd =>
    intro thread inactive
    by_cases eq : thread=selected
    · subst thread
      have bad := inv selected inactive
      simp [outside,fetch] at bad
    · simpa [setLane,Function.update,eq] using inv thread inactive
  | skip =>
    intro thread inactive
    by_cases eq : thread=selected
    · subst thread
      obtain ⟨count,target⟩ := bounds.1 _ _ _ fetch
      simp only [setLane,Function.update_self]
      split
      · omega
      · exact target
    · simpa [setLane,Function.update,eq] using inv thread inactive
  | @sync resource =>
    intro thread inactive
    simp only [synchronize]
    split
    · exact inv thread inactive
    · exact inv thread inactive
    · rename_i released
      have same := release_aligned cfg s selected resource aligned released thread
      simpa [advance,same] using bounds.2 _ _ fetch

theorem runs_invariant (run : Runs cfg program start events final)
    (aligned : Aligned start) (inv : Invariant program active start) (bounds : Boundaries program active) :
    Invariant program active final := by
  induction run with
  | nil => exact inv
  | cons step tail ih => exact ih (step_aligned step aligned) (step_invariant step aligned inv bounds)

/-- Padding produces neither loads nor stores under the checked boundary rules. -/
theorem access_active (run : Runs cfg program start events final)
    (aligned : Aligned start) (inv : Invariant program active start) (bounds : Boundaries program active)
    (member : Event.data thread access∈events) : thread.val<active := by
  obtain ⟨before,earlier,selected,out,suffix,hp,hs,hm,ht,he⟩ := run_access_prefix run member
  obtain ⟨eq,op,next,fetch,hd⟩ := step_access_origin hs hm
  subst selected
  by_contra inactive
  have bad := runs_invariant hp aligned inv bounds thread (by omega)
  simp [outside,fetch] at bad

end PtxTorchLean.Poisson.PTX.Concurrent.Padding

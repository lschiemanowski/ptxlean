import PoissonPTX.ConcurrentAddress

/-! Address preparation may survive intervening loads and arithmetic. Stores
clear the fact, so inactive lanes may jump directly to the following barrier. -/
namespace PtxTorchLean.Poisson.PTX.Concurrent.AddressHold
open Ptx
open Address (Tag Ready Keeps data_keeps)

def keep (r : Nat) : Op → Bool
  | .mov d _ | .mul32 d _ _ | .add32 d _ _ | .add64 d _ _ |
    .wide8 d _ | .load64 _ d _ | .fp _ d _ _ => r != d
  | .store64 _ _ _ => true

theorem keep_correct : keep r op=true ↔ SharedStore.keeps r op := by
  cases op <;> simp [keep,SharedStore.keeps]

def nextTag (old : Tag) (i : Instr) : Tag :=
  if Address.nextTag old i≠.none then Address.nextTag old i else
  match i with
  | .data (.store64 ..) => .none
  | .data op => if keep 1 op && keep 2 op then old else .none
  | _ => .none

def tag (program : List Instr) (pc : Nat) : Tag :=
  (program.take pc).foldl nextTag .none

theorem tag_zero : tag program 0=.none := rfl

theorem tag_next (fetch : program[pc]?=some i) : tag program (pc+1)=nextTag (tag program pc) i := by
  unfold tag
  rw [List.take_add_one]
  simp [fetch,List.foldl_append]

theorem ready_kept (h : Data op s t effect) (ready : Ready old s)
    (base : SharedStore.keeps 3 op) (lane : SharedStore.keeps 14 op)
    (scaled : SharedStore.keeps 1 op) (addressed : SharedStore.keeps 2 op) : Ready old t := by
  cases old <;> simp only [Ready] at ready ⊢
  · rw [data_keeps h scaled]; simpa only [wide,data_keeps h lane] using ready
  · rw [data_keeps h addressed,data_keeps h base]
    simpa only [wide,data_keeps h lane] using ready

theorem data_ready (h : Data op s t effect) (ready : Ready old s)
    (base : SharedStore.keeps 3 op) (lane : SharedStore.keeps 14 op) :
    Ready (nextTag old (.data op)) t := by
  unfold nextTag
  split
  · exact Address.data_ready h ready base lane
  · cases op <;> simp only <;> try { trivial }
    all_goals
      split
      · rename_i frame
        simp only [Bool.and_eq_true] at frame
        have frames := frame
        exact ready_kept h ready base lane (keep_correct.mp frames.1) (keep_correct.mp frames.2)
      · trivial

/-- All jumps enter where no scratch preparation is presumed. -/
def Entries (program : List Instr) : Prop :=
  ∀ pc active target : Nat, program[pc]?=some (.skip active target) → tag program target=.none

def Invariant (program : List Instr) (s : State n) : Prop :=
  ∀ thread, Ready (tag program (s.lanes thread).pc) (s.lanes thread)

theorem step_invariant {s : State n} (step : Step cfg program selected s out)
    (aligned : Aligned s) (inv : Invariant program s) (entries : Entries program)
    (base : Keeps program 3) (lane : Keeps program 14) : Invariant program out.state := by
  have saved := step
  obtain ⟨fresh,i,fetch,h⟩ := step
  cases h with
  | data hd =>
    intro thread
    by_cases eq : thread=selected
    · subst thread
      simp only [setLane,Function.update_self]
      rw [data_pc hd,tag_next fetch]
      exact data_ready hd (inv selected) (base _ _ fetch) (lane _ _ fetch)
    · simpa [setLane,Function.update,eq] using inv thread
  | skip =>
    intro thread
    by_cases eq : thread=selected
    · subst thread
      simp only [setLane,Function.update_self]
      split
      · rw [tag_next fetch]; simp [nextTag,Address.nextTag,Ready]
      · rw [entries _ _ _ fetch]; trivial
    · simpa [setLane,Function.update,eq] using inv thread
  | @sync resource =>
    intro thread
    simp only [synchronize]
    split
    · exact inv thread
    · exact inv thread
    · rename_i released
      have same := release_aligned cfg s selected resource aligned released thread
      change Ready (tag program ((s.lanes thread).pc+1)) (advance (s.lanes thread))
      rw [same,tag_next fetch]
      simp [nextTag,Address.nextTag,Ready]

theorem runs_invariant (run : Runs cfg program start events final)
    (aligned : Aligned start) (inv : Invariant program start) (entries : Entries program)
    (base : Keeps program 3) (lane : Keeps program 14) : Invariant program final := by
  induction run with
  | nil => exact inv
  | cons step tail ih => exact ih (step_aligned step aligned) (step_invariant step aligned inv entries base lane)

end PtxTorchLean.Poisson.PTX.Concurrent.AddressHold

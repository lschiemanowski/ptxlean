import PoissonPTX.ConcurrentOwnership

/-! A small syntactic invariant for the generated shared-store preparation.
It tracks no floating-point values and imposes no read-source conditions. -/
namespace PtxTorchLean.Poisson.PTX.Concurrent.Address
open Ptx

inductive Tag where
  | none | scaled | addressed
  deriving DecidableEq, Repr

def nextTag (old : Tag) : Instr → Tag
  | .data (.wide8 1 (.reg 14)) => .scaled
  | .data (.add64 2 (.reg 3) (.reg 1)) => if old=.scaled then .addressed else .none
  | _ => .none

def tag (program : List Instr) (pc : Nat) : Tag :=
  (program.take pc).foldl nextTag .none

theorem tag_zero : tag program 0=.none := rfl

theorem tag_next (fetch : program[pc]?=some i) : tag program (pc+1)=nextTag (tag program pc) i := by
  unfold tag
  rw [List.take_add_one]
  simp [fetch,List.foldl_append]

def Ready (kind : Tag) (s : PTX.State) : Prop :=
  match kind with
  | .none => True
  | .scaled => s.regs 1=wide s 14
  | .addressed => s.regs 2=s.regs 3+wide s 14

def Keeps (program : List Instr) (r : Nat) : Prop :=
  ∀ (pc : Nat) op, program[pc]?=some (.data op) → SharedStore.keeps r op

theorem data_keeps (h : Data op s t effect) (frame : SharedStore.keeps r op) : t.regs r=s.regs r := by
  cases h with
  | ordinary plain he => exact SharedStore.eval_keeps he frame
  | load => simp_all [SharedStore.keeps,assign,advance]
  | store => cases ‹Space› <;> rfl

theorem data_ready (h : Data op s t effect) (ready : Ready old s)
    (base : SharedStore.keeps 3 op) (lane : SharedStore.keeps 14 op) :
    Ready (nextTag old (.data op)) t := by
  cases op <;> try { simp [nextTag,Ready] }
  case wide8 dst index =>
    by_cases hd : dst=1
    · subst dst
      cases index <;> simp only [nextTag] <;> try { trivial }
      rename_i r
      by_cases hr : r=14
      · subst r
        cases h with
        | ordinary plain he =>
          cases he
          simp [Ready,wide,assign,advance,Operand.eval]
      · simp [hr,Ready]
    · simp [nextTag,hd,Ready]
  case add64 dst a b =>
    by_cases hd : dst=2
    · subst dst
      cases a <;> simp only [nextTag] <;> try { trivial }
      rename_i ra
      by_cases ha : ra=3
      · subst ra
        cases b <;> try { simp only [nextTag] } <;> try { trivial }
        rename_i rb
        by_cases hb : rb=1
        · subst rb
          cases old <;> simp only [nextTag,Ready] at ready ⊢ <;> try trivial
          cases h with
          | ordinary plain he =>
            cases he
            simp [assign,advance,Operand.eval,wide,ready]
        · simp [hb,Ready]
      · simp [ha,Ready]
    · simp [nextTag,hd,Ready]

/-- All jumps enter where no scratch preparation is presumed. -/
def Entries (program : List Instr) : Prop :=
  ∀ pc active target : Nat, program[pc]?=some (.skip active target) → tag program target=.none

def Invariant (program : List Instr) (s : State n) : Prop :=
  ∀ thread, Ready (tag program (s.lanes thread).pc) (s.lanes thread)

theorem step_keeps {s : State n} (step : Step cfg program selected s out)
    (frame : Keeps program r) (thread : Fin n) :
    (out.state.lanes thread).regs r=(s.lanes thread).regs r := by
  obtain ⟨fresh,i,fetch,h⟩ := step
  cases h with
  | data hd =>
    by_cases eq : thread=selected
    · subst thread; simpa [setLane] using data_keeps hd (frame _ _ fetch)
    · simp [setLane,Function.update,eq]
  | skip => by_cases eq : thread=selected <;> simp [setLane,Function.update,eq]
  | sync => simp only [synchronize]; split <;> rfl

theorem runs_keeps {s : State n} (run : Runs cfg program s events final)
    (frame : Keeps program r) (thread : Fin n) :
    (final.lanes thread).regs r=(s.lanes thread).regs r := by
  induction run with
  | nil => rfl
  | cons step tail ih => exact ih.trans (step_keeps step frame thread)

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
      · rw [tag_next fetch]; trivial
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
      trivial

theorem runs_invariant (run : Runs cfg program start events final)
    (aligned : Aligned start) (inv : Invariant program start) (entries : Entries program)
    (base : Keeps program 3) (lane : Keeps program 14) : Invariant program final := by
  induction run with
  | nil => exact inv
  | cons step tail ih => exact ih (step_aligned step aligned) (step_invariant step aligned inv entries base lane)

end PtxTorchLean.Poisson.PTX.Concurrent.Address

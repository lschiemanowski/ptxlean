import PoissonPTX.ProjectionBuild
import PoissonPTX.CellFinalKernel

/-! One fetched concurrent machine with a barrier-capable front and a fetched
per-thread tail. Tail instruction rules are reused from Kernel.Eval. No ghost
arithmetic state or projected execution is part of the machine state. -/
namespace PtxTorchLean.Poisson.PTX.Concurrent.WithTail

structure State (n : Nat) where
  core : Concurrent.State n
  predicate : Fin n → Bool
  halted : Fin n → Bool

structure Outcome (n : Nat) where
  state : State n
  events : List (Event n)

def lane (s : State n) (thread : Fin n) : Kernel.State :=
  ⟨s.core.lanes thread,s.predicate thread,s.halted thread⟩

def update (s : State n) (thread : Fin n) (next : Kernel.State) : State n :=
  ⟨setLane s.core thread next.core,Function.update s.predicate thread next.predicate,
    Function.update s.halted thread next.halted⟩

/-- Record actual memory operands and values, not desired numerical results. -/
def access (i : Kernel.Instr) (s t : Kernel.State) : Option Access :=
  match i with
  | .data (.store64 sp addr src) => some ⟨sp,⟨s.core.pc,true,(addr.eval s.core).toNat,src.eval s.core⟩⟩
  | .data (.load64 sp dst addr) => some ⟨sp,⟨s.core.pc,false,(addr.eval s.core).toNat,t.core.regs dst⟩⟩
  | _ => none

inductive Step (cfg : Config n) (ctx : Fin n → Kernel.Context)
    (front : List Instr) (tail : List Kernel.Instr) : Fin n → State n → Outcome n → Prop where
  | front (running : s.halted thread=false) (step : Concurrent.Step cfg front thread s.core out) :
      Step cfg ctx front tail thread s ⟨{s with core:=out.state},out.events⟩
  | tail (running : s.halted thread=false) (fresh : s.core.barrier.arrived thread=false)
      (past : front.length≤(s.core.lanes thread).pc)
      (fetch : tail[(s.core.lanes thread).pc-front.length]?=some i)
      (eval : Kernel.Eval (ctx thread) i (lane s thread) next) :
      Step cfg ctx front tail thread s
        ⟨update s thread next,(access i (lane s thread) next).toList.map (Event.data thread)⟩

inductive Runs (cfg : Config n) (ctx : Fin n → Kernel.Context)
    (front : List Instr) (tail : List Kernel.Instr) : State n → List (Event n) → State n → Prop where
  | nil : Runs cfg ctx front tail s [] s
  | cons : Step cfg ctx front tail thread s out → Runs cfg ctx front tail out.state rest final →
      Runs cfg ctx front tail s (out.events++rest) final

theorem halted_blocks (halted : s.halted thread=true) : ¬Step cfg ctx front tail thread s out := by
  intro h; cases h <;> simp_all

theorem step_aligned (step : Step cfg ctx front tail thread s out) (aligned : Aligned s.core) :
    Aligned out.state.core := by
  cases step with
  | front _ h => exact Concurrent.step_aligned h aligned
  | tail _ fresh _ _ _ => exact setLane_aligned aligned fresh _

def keeps (r : Nat) : Kernel.Instr → Prop
  | .parameter dst | .lane dst | .group dst | .mad32 dst _ _ _ => r≠dst
  | .data op => SharedStore.keeps r op
  | _ => True

instance : Decidable (keeps r i) := by
  cases i <;> simp only [keeps] <;> try infer_instance
  cases ‹Op› <;> simp only [SharedStore.keeps] <;> infer_instance

theorem eval_keeps (h : Kernel.Eval ctx i s t) (frame : keeps r i) : t.core.regs r=s.core.regs r := by
  cases h with
  | data he => exact SharedStore.eval_keeps he frame
  | simple ordinary =>
    cases i <;> simp_all [keeps,Kernel.simple,Kernel.scalar,Kernel.advance,Kernel.halt,assign,PTX.advance]
    split <;> rfl

/-- Tail branch targets are clamped only in the projected arithmetic program. -/
def clip (cut : Nat) : Instr → Instr
  | .skip active target => .skip active (min target cut)
  | i => i

/-- Live arithmetic lanes retain their whole state. Once a lane reaches the tail,
its projected lane is at the arithmetic cutoff and retains the tracked register.
The tail's scratch registers and output memory need not stay frozen. -/
def Related (cut tracked : Nat) (actual shadow : Concurrent.State n) : Prop :=
  actual.barrier=shadow.barrier ∧ actual.site=shadow.site ∧ ∀ t,
    if (actual.lanes t).pc<cut then actual.lanes t=shadow.lanes t
    else (shadow.lanes t).pc=cut ∧ (actual.lanes t).regs tracked=(shadow.lanes t).regs tracked

theorem related_refl {s : Concurrent.State n} (bounded : ∀ t, (s.lanes t).pc≤cut) : Related cut tracked s s := by
  refine ⟨rfl,rfl,?_⟩
  intro t; split
  · rfl
  · exact ⟨by have := bounded t; omega,rfl⟩

theorem related_live (related : Related cut tracked actual shadow) (before : (actual.lanes t).pc<cut) :
    actual.lanes t=shadow.lanes t := by simpa [before] using related.2.2 t

/-- Front steps replace only the selected lane, normalizing its projected PC. -/
theorem related_update (related : Related cut tracked actual shadow)
    (pc : projected.pc=min next.pc cut) (regs : next.regs tracked=projected.regs tracked)
    (live : next.pc<cut → next=projected) :
    Related cut tracked (setLane actual t next) (setLane shadow t projected) := by
  refine ⟨related.1,related.2.1,?_⟩
  intro u
  by_cases eq : u=t
  · subst u; simp only [setLane,Function.update_self]
    split
    · exact live ‹_›
    · exact ⟨by rw [pc,Nat.min_eq_right (by omega)],regs⟩
  · simpa [setLane,Function.update,eq] using related.2.2 u

end PtxTorchLean.Poisson.PTX.Concurrent.WithTail

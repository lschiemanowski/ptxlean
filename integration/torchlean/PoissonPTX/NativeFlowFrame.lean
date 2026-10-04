import PoissonPTX.NativeFlow
import PoissonPTX.IndexedFrames

namespace PtxTorchLean.Poisson.PTX.Concurrent.NativeFlow

def keeps (r : Nat) : Flow.Instr → Prop
  | .data op => Indexed.keeps r op
  | .context dst _ | .select _ _ dst _ => r≠dst
  | _ => True

theorem data_keeps (actual : Indexed.Candidate.Data op s t access index)
    (frame : Indexed.keeps r op) : t.regs r=s.regs r := by
  cases actual with
  | data one =>
    cases one with
    | ordinary _ execution => exact SharedStore.eval_keeps execution frame
    | load => simp_all [Indexed.keeps,SharedStore.keeps,assign,advance]
    | store => cases ‹Space› <;> rfl
  | _ => simp_all [Indexed.keeps,assign,advance]

theorem eval_keeps (actual : Flow.Observed.Eval ctx i s t access index)
    (frame : keeps r i) : t.core.regs r=s.core.regs r := by
  cases actual with
  | data one => exact data_keeps one frame
  | simple =>
    cases i <;> simp_all [keeps,Flow.simple,Flow.next,Flow.goto,Flow.halt,assign,advance]
    all_goals split <;> simp_all

/-- A lane invariant is checked across its real ordinary steps and barrier
advances. A barrier can advance a lane only at the fetched barrier site. -/
theorem step_lanes {P : Fin n → Flow.State → Prop}
    (actual : Step cfg ctx program selected s out) (aligned : Aligned s.core)
    (initial : ∀ owner, P owner (lane s owner))
    (flow : ∀ owner i before after access index, P owner before →
      program[before.core.pc]?=some (.flow i) →
      Flow.Observed.Eval (ctx owner) i before after access index → P owner after)
    (sync : ∀ owner before resource, P owner before →
      program[before.core.pc]?=some (.sync resource) → P owner (Flow.next before)) :
    ∀ owner, P owner (lane out.state owner) := by
  cases actual with
  | flow running fresh fetch execution =>
    intro owner
    by_cases same : owner=selected
    · subst owner
      rw [lane_update_self]
      exact flow _ _ _ _ _ _ (initial _) fetch execution
    · rw [lane_update_other _ _ _ same]; exact initial _
  | @sync _ resource running fresh fetch =>
    intro owner
    by_cases release : (Ptx.Barrier.step (barrierConfig cfg s.core selected) s.core.barrier
        (barrierRequest cfg s.core selected resource)).disposition=.released
    · have site := release_aligned cfg s.core selected resource aligned release owner
      have atSite : program[(lane s owner).core.pc]?=some (.sync resource) := by
        simpa only [lane,site] using fetch
      simpa only [synchronize,release,Flow.next,lane] using sync owner (lane s owner) resource (initial _) atSite
    · simp only [synchronize]
      split <;> try exact initial _
      exact False.elim (release (by assumption))

theorem runs_lanes {P : Fin n → Flow.State → Prop}
    (actual : Runs cfg ctx program s events indices t) (aligned : Aligned s.core)
    (initial : ∀ owner, P owner (lane s owner))
    (flow : ∀ owner i before after access index, P owner before →
      program[before.core.pc]?=some (.flow i) →
      Flow.Observed.Eval (ctx owner) i before after access index → P owner after)
    (sync : ∀ owner before resource, P owner before →
      program[before.core.pc]?=some (.sync resource) → P owner (Flow.next before)) :
    ∀ owner, P owner (lane t owner) := by
  induction actual with
  | nil => exact initial
  | cons one rest ih => exact ih (step_aligned one aligned) (step_lanes one aligned initial flow sync)

end PtxTorchLean.Poisson.PTX.Concurrent.NativeFlow

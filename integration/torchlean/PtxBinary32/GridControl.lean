import PtxBinary32.GridExecution
import PtxBinary32.ParallelControl

/-! Actual trace positions and per-thread instruction order across a grid. -/
namespace Ptx.Scalar.Parallel.Grid.Control
open Parallel.Control (Straight)

def stamp (e : Event groups n) : Option ((Fin groups × Fin n) × Nat) :=
  (Parallel.Control.stamp e.2).map (fun p => ((e.1,p.1),p.2))
def cursor (s : State groups n) (t : Fin groups × Fin n) : Nat :=
  Parallel.Control.cursor (view s t.1) t.2

theorem cursor_bounds (s : State groups n) (t : Fin groups × Fin n) :
    2*((s.blocks t.1).lanes t.2).scalar.pc ≤ cursor s t ∧
    cursor s t ≤ 2*((s.blocks t.1).lanes t.2).scalar.pc+1 :=
  Parallel.Control.cursor_bounds (view s t.1) t.2

structure Progress (s : State groups n) (events : List (Event groups n)) (final : State groups n) : Prop where
  monotone : ∀ t, cursor s t ≤ cursor final t
  emitted : ∀ (pos : Nat) e t pc, events[pos]?=some e → stamp e=some (t,pc) →
    cursor s t=2*pc ∧ 2*pc<cursor final t
  unique : ∀ (p q : Nat) e f t u pc qc, events[p]?=some e → events[q]?=some f →
    stamp e=some (t,pc) → stamp f=some (u,qc) → p=q

private theorem tagged {g : Fin groups} {e : Parallel.Event n} {t : Fin groups × Fin n} {pc : Nat}
    (h : stamp (g,e)=some (t,pc)) : g=t.1 ∧ Parallel.Control.stamp e=some (t.2,pc) := by
  simp only [stamp,Option.map_eq_some_iff] at h
  obtain ⟨⟨u,q⟩,he,eq⟩ := h
  cases eq
  exact ⟨rfl,he⟩

private theorem tag_at {g : Fin groups} {events : List (Parallel.Event n)} {p : Nat} {e : Event groups n}
    (h : (tag g events)[p]?=some e) : ∃ f, events[p]?=some f ∧ e=(g,f) := by
  simpa [tag,List.getElem?_map,Option.map_eq_some_iff,eq_comm] using h

theorem step_progress {s final : State groups n} {events : List (Event groups n)}
    (step : Step cfg program s events final) (straight : Straight program) : Progress s events final := by
  cases step with
  | issue g t candidate out step =>
    have now := Parallel.Control.step_progress step straight
    refine ⟨?_,?_,?_⟩
    · intro u
      by_cases same : u.1=g
      · simpa [cursor,same] using now.monotone u.2
      · simp [cursor,view_install_other _ _ _ _ same,Parallel.Control.cursor]
    · intro pos e u pc hp he
      obtain ⟨f,hf,rfl⟩ := tag_at hp
      obtain ⟨hg,tagged⟩ := tagged he
      simpa [cursor,← hg] using now.emitted pos f u.2 pc hf tagged
    · intro p q e f u v pc qc hp hq he hf
      obtain ⟨e,ep,rfl⟩ := tag_at hp
      obtain ⟨f,fq,rfl⟩ := tag_at hq
      exact now.unique p q e f u.2 v.2 pc qc ep fq (tagged he).2 (tagged hf).2

/-- Bounds and strict per-thread order for a whole, possibly unfinished trace. -/
structure TraceProgress (s : State groups n) (events : List (Event groups n)) (final : State groups n) : Prop where
  monotone : ∀ t, cursor s t ≤ cursor final t
  emitted : ∀ (pos : Nat) e t pc, events[pos]? = some e → stamp e = some (t,pc) →
    cursor s t ≤ 2*pc ∧ 2*pc < cursor final t
  ordered : ∀ (p q : Nat) e f t pc qc, p<q → events[p]? = some e → events[q]? = some f →
    stamp e = some (t,pc) → stamp f = some (t,qc) → pc<qc

theorem runs_progress (run : Runs cfg program s events final) (straight : Straight program) :
    TraceProgress s events final := by
  induction run with
  | nil => exact ⟨fun _ => Nat.le_refl _,by intros; simp_all,by intros; simp_all⟩
  | @cons s added middle rest final step run ih =>
    have now := step_progress step straight
    refine ⟨fun t => (now.monotone t).trans (ih.monotone t),?_,?_⟩
    · intro pos e t pc atPos tagged
      by_cases early : pos < added.length
      · have h : added[pos]? = some e := by simpa [List.getElem?_append,early] using atPos
        have bounds := now.emitted pos e t pc h tagged
        exact ⟨Nat.le_of_eq bounds.1,(bounds.2).trans_le (ih.monotone t)⟩
      · have h : rest[pos-added.length]? = some e := by simpa [List.getElem?_append,early] using atPos
        have bounds := ih.emitted _ e t pc h tagged
        exact ⟨(now.monotone t).trans bounds.1,bounds.2⟩
    · intro p q e f t pc qc earlier hp hq he hf
      by_cases pe : p < added.length
      · have atP : added[p]? = some e := by simpa [List.getElem?_append,pe] using hp
        by_cases qe : q < added.length
        · have atQ : added[q]? = some f := by simpa [List.getElem?_append,qe] using hq
          have := now.unique p q e f t t pc qc atP atQ he hf
          omega
        · have atQ : rest[q-added.length]? = some f := by simpa [List.getElem?_append,qe] using hq
          have first := (now.emitted p e t pc atP he).2
          have second := (ih.emitted _ f t qc atQ hf).1
          omega
      · have qe : ¬q < added.length := by omega
        have atP : rest[p-added.length]? = some e := by simpa [List.getElem?_append,pe] using hp
        have atQ : rest[q-added.length]? = some f := by simpa [List.getElem?_append,qe] using hq
        exact ih.ordered _ _ e f t pc qc (by omega) atP atQ he hf

/-- A single thread cannot issue the same instruction site twice. -/
theorem same_site_unique {s final : State groups n} {events : List (Event groups n)} (run : Runs cfg program s events final) (straight : Straight program)
    (p q : Nat) (e f : Event groups n) (t : (Fin groups × Fin n)) (pc : Nat)
    (hp : events[p]? = some e) (hq : events[q]? = some f)
    (he : stamp e = some (t,pc)) (hf : stamp f = some (t,pc)) : p=q := by
  have order := (runs_progress run straight).ordered
  rcases lt_trichotomy p q with before | same | after
  · have := order p q e f t pc pc before hp hq he hf; omega
  · exact same
  · have := order q p f e t pc pc after hq hp hf he; omega

/-- Instruction positions recover the actual order of a thread's events. -/
theorem position_iff_pc {s final : State groups n} {events : List (Event groups n)} (run : Runs cfg program s events final) (straight : Straight program)
    (p q : Nat) (e f : Event groups n) (t : (Fin groups × Fin n)) (pc qc : Nat)
    (hp : events[p]? = some e) (hq : events[q]? = some f)
    (he : stamp e = some (t,pc)) (hf : stamp f = some (t,qc)) : p<q ↔ pc<qc := by
  have order := (runs_progress run straight).ordered
  constructor
  · exact fun h => order p q e f t pc qc h hp hq he hf
  · intro h
    rcases lt_trichotomy p q with before | same | after
    · exact before
    · subst q
      have eq : e=f := Option.some.inj (hp.symm.trans hq)
      subst f
      have pair := Option.some.inj (he.symm.trans hf)
      have := congrArg Prod.snd pair
      omega
    · have := order q p f e t qc pc after hq hp hf he; omega

end Ptx.Scalar.Parallel.Grid.Control

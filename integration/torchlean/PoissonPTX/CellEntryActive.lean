import PoissonPTX.CellEntryControl

namespace PtxTorchLean.Poisson.PTX.CellEntry.Control

/-- Only lanes which took the live branch can occupy a gather instruction. -/
def Active (s : CellPrologue.State) : Prop :=
  8≤s.core.pc → s.core.pc<20 → s.live=true

theorem active_initial (pc : s.core.pc=0) : Active s := by simp [Active,pc]

theorem setup_pc (fetch : (program width cells source)[pc]?=some (.setup op)) : pc<7 := by
  have bound := (List.getElem?_eq_some_iff.mp fetch).1
  rw [program_length] at bound
  interval_cases pc <;> simp_all [program,CellPrologue.program,CellGather.code]

theorem setup_next (step : CellPrologue.eval ctx op s=some t) : t.core.pc=s.core.pc+1 :=
  CellEntry.setup_pc step

variable {n : Nat} {s t : State n} {out : Outcome n} {cfg : Concurrent.Config n}
  {ctx : Fin n → CellPrologue.Context}

theorem active_step (actual : Step cfg ctx (program width cells source) selected s out)
    (aligned : Concurrent.Aligned s.core) (active : ∀ u, Active (lane s u)) :
    ∀ u, Active (lane out.state u) := by
  intro owner lo hi
  obtain ⟨fresh,i,fetch,dispatch⟩ := actual
  cases dispatch with
  | setup he =>
    by_cases same : owner=selected
    · subst owner
      have next := setup_next he
      have before := setup_pc fetch
      simp only [lane,setLane,Concurrent.setLane,Function.update_self] at lo
      change _≤_ at lo
      change (lane s selected).core.pc<7 at before
      omega
    · simpa [Active,lane,setLane,Concurrent.setLane,Function.update,same] using
        active owner (by simpa [lane,setLane,Concurrent.setLane,Function.update,same] using lo)
          (by simpa [lane,setLane,Concurrent.setLane,Function.update,same] using hi)
  | gather he =>
    by_cases same : owner=selected
    · subst owner
      have past := gather_past fetch
      have notGuard : (s.core.lanes selected).pc≠7 := by
        intro h; simp [h,program,CellPrologue.program,CellGather.code] at fetch
      have next := Indexed.Candidate.data_pc he
      simp only [lane,Concurrent.setLane,Function.update_self] at lo hi ⊢
      exact active selected (by change 8≤(s.core.lanes selected).pc; omega)
        (by change (s.core.lanes selected).pc<20; omega)
    · simpa [lane,Concurrent.setLane,Function.update,same] using
        active owner (by simpa [lane,Concurrent.setLane,Function.update,same] using lo)
          (by simpa [lane,Concurrent.setLane,Function.update,same] using hi)
  | skip =>
    have pc := skip_pc fetch
    have target : ‹Nat›=20 := by simpa [pc,program,CellPrologue.program,CellGather.code] using fetch.symm
    by_cases same : owner=selected
    · subst owner
      simp only [lane,Concurrent.setLane,Function.update_self] at lo hi ⊢
      cases h : s.live selected <;> simp_all
    · simpa [lane,Concurrent.setLane,Function.update,same] using
        active owner (by simpa [lane,Concurrent.setLane,Function.update,same] using lo)
          (by simpa [lane,Concurrent.setLane,Function.update,same] using hi)
  | sync =>
    simp only [synchronize,Concurrent.synchronize] at lo hi ⊢
    split at hi
    · simp_all only; exact active owner lo hi
    · simp_all only; exact active owner lo hi
    · rename_i released
      have pc := (Concurrent.release_aligned cfg s.core selected 0 aligned released owner).trans (sync_pc fetch)
      change (s.core.lanes owner).pc+1<20 at hi
      omega

theorem active_run (run : Runs cfg ctx (program width cells source) s events indices t)
    (aligned : Concurrent.Aligned s.core) (active : ∀ u, Active (lane s u)) :
    ∀ u, Active (lane t u) := by
  induction run with
  | nil => exact active
  | cons one _ ih => exact ih (step_aligned one aligned) (active_step one aligned active)

/-- An arbitrary candidate run from entry cannot reach an active gather counter
with a padding lane, regardless of chosen memory bits. -/
theorem live_gather (run : Runs cfg ctx (program width cells source) s events indices t)
    (aligned : Concurrent.Aligned s.core) (pcs : ∀ u, (s.core.lanes u).pc=0)
    (positive : 0<width) (fits : width*width<2^32)
    (lo : 8≤(t.core.lanes owner).pc) (hi : (t.core.lanes owner).pc<20) :
    (ctx owner).lane.toNat<width*width := by
  have control := from_run run aligned (fun u => initial (s:=lane s u) (pcs u)) positive fits
  have active := active_run run aligned (fun u => active_initial (s:=lane s u) (pcs u)) owner lo hi
  have guard := (control owner).2.2.2.2.1 (by change 5≤(t.core.lanes owner).pc; omega)
  rw [guard] at active
  exact of_decide_eq_true active

end PtxTorchLean.Poisson.PTX.CellEntry.Control

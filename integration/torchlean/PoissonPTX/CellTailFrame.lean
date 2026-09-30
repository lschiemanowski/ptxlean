import PoissonPTX.CellTailShape

namespace PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.WithOutput.Address
variable {n : Nat} {cfg : Config n} {ctx : Fin n → Kernel.Context}
  {s start final : WithTail.State n} {out : WithTail.Outcome n}
  {events : List (Event n)} {selected : Fin n}

theorem step_keeps (lo : 2≤width) (hi : width≤5)
    (step : WithTail.Step cfg ctx (front width) (CellFinal.tail width output) selected s out)
    (reg : r=0 ∨ r=14 ∨ r=15) (t : Fin n) :
    (out.state.core.lanes t).regs r=(s.core.lanes t).regs r := by
  cases step with
  | front _ h => exact Concurrent.Address.step_keeps h (front_keeps lo hi reg) t
  | tail _ _ _ fetch eval =>
    by_cases eq : t=selected
    · subst t
      simpa only [WithTail.update,WithTail.lane,setLane,Function.update_self] using
        WithTail.eval_keeps eval (tail_keeps_register reg _ (List.mem_of_getElem? fetch))
    · simp [WithTail.update,setLane,Function.update,eq]

theorem runs_keeps (lo : 2≤width) (hi : width≤5)
    (run : WithTail.Runs cfg ctx (front width) (CellFinal.tail width output) start events final)
    (reg : r=0 ∨ r=14 ∨ r=15) (t : Fin n) :
    (final.core.lanes t).regs r=(start.core.lanes t).regs r := by
  induction run with
  | nil => rfl
  | cons step _ ih => exact ih.trans (step_keeps lo hi step reg t)

/-- The output address in a later state equals the one determined at launch,
even though scratch registers and byte memories have changed. -/
theorem runs_location (lo : 2≤width) (hi : width≤5)
    (run : WithTail.Runs cfg ctx (front width) (CellFinal.tail width output) start events final)
    (t : Fin n) :
    CellFinal.location (final.core.lanes t) width output=
      CellFinal.location (start.core.lanes t) width output :=
  location_eq (runs_keeps lo hi run (Or.inl rfl) t)
    (runs_keeps lo hi run (Or.inr (Or.inl rfl)) t)
    (runs_keeps lo hi run (Or.inr (Or.inr rfl)) t)

theorem initial_ready (pcs : ∀ t, (start.core.lanes t).pc=0) : Invariant width output start := by
  intro t
  exact ready_before (by rw [pcs]; omega)

/-- Extract the actual local word after the active lane has executed its store.
This is per-lane memory; combining writers into one global tensor is separate. -/
theorem stored_word (lo : 2≤width) (hi : width≤5)
    (run : WithTail.Runs cfg ctx (front width) (CellFinal.tail width output) start events final)
    (aligned : Aligned start.core) (pcs : ∀ t, (start.core.lanes t).pc=0)
    (t : Fin n) (active : t.val<width*width)
    (finished : (front width).length+5≤(final.core.lanes t).pc) :
    read64 (final.core.lanes t).global (CellFinal.location (start.core.lanes t) width output).toNat=
      (final.core.lanes t).regs 11 := by
  have invariant := runs_ready lo hi run aligned (initial_ready pcs) t
  rw [← runs_location lo hi run t]
  exact invariant.2.2.2.2 finished active

end PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.WithOutput.Address

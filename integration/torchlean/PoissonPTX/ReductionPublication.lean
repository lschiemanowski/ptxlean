import PoissonPTX.ReductionOwnership
import PoissonPTX.ConcurrentProducer

/-! A later access proves the preceding tree publication actually occurred.
The shared-tree guards and barriers supply the causal path; the caller does
not supply a chosen write occurrence or a preconstructed barrier edge. -/
namespace PtxTorchLean.Poisson.PTX.Concurrent.Reduction.Control

/-- The initial publication spells out a zero offset; later stores use r2. -/
def storeAddress (k : Fin 9) : Operand := if k.val=0 then .offset 2 0 else .reg 2

theorem store_fetch : ∀ k : Fin 9,
    program[site k]?=some (.data (.store64 .shared (storeAddress k) (.reg 8))) := by
  decide +kernel

theorem barrier_fetch : ∀ k : Fin 9, program[site k+1]?=some (.sync 0) := by decide +kernel

/-- Before a publication, a guard either admits every required writer or
jumps no farther than that store. -/
theorem checked_writer_paths : ∀ (k : Fin 9) (pc : Fin 68),
    (match program[pc.val]? with
    | some (.skip count target) => decide (pc.val≤site k → active k≤count ∨ target≤site k)
    | _ => true)=true := by decide +kernel

theorem writer_stops (k : Fin 9) (writer : Fin 256) (live : writer.val<active k) :
    StopsFor program writer (site k) := by
  intro pc count target fetch earlier
  have h := checked_writer_paths k ⟨pc,by
    have h := (List.getElem?_eq_some_iff.mp fetch).1; simpa only [length] using h⟩
  simp only [fetch,decide_eq_true_eq] at h
  have bounds := h earlier
  omega

theorem checked_barrier_paths : ∀ (k : Fin 9) (pc : Fin 68),
    (match program[pc.val]? with
    | some (.skip _ target) => decide (pc.val≤site k+1 → target≤site k+1)
    | _ => true)=true := by decide +kernel

theorem barrier_stops (k : Fin 9) : StopsAt program (site k+1) := by
  intro pc count target fetch earlier
  have h := checked_barrier_paths k ⟨pc,by
    have h := (List.getElem?_eq_some_iff.mp fetch).1; simpa only [length] using h⟩
  simp only [fetch,decide_eq_true_eq] at h
  exact h earlier

/-- Arbitrary actual interleavings yield the selected producer and a real
store/arrival/completion/read causal edge for every earlier active writer. -/
theorem published {start : State 256} (run : Runs cfg program start events final)
    (reset : start.barrier=Ptx.Barrier.reset generation)
    (entry : ∀ t, (start.lanes t).pc=0)
    (k : Fin 9) (writer : Fin 256) (live : writer.val<active k)
    (observed : events[r]?=some (.data reader access)) (later : site k+1<access.data.pc) :
    ∃ w wa, events[w]?=some (.data writer wa) ∧ wa.data.pc=site k ∧
      wa.data.store=true ∧ wa.space=.shared ∧ Visibility.Across events w r := by
  exact producer_across run reset (store_fetch k) (writer_stops k writer live)
    (by rw [entry]; omega) (by omega) (barrier_fetch k) (barrier_stops k)
    (by intro t; rw [entry]; omega) observed later

end PtxTorchLean.Poisson.PTX.Concurrent.Reduction.Control

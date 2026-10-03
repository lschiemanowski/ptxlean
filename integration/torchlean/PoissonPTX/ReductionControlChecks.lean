import PoissonPTX.ReductionReads

/-! Negative control/address regressions. These test that key certificates do
not silently admit extra writers, skipped barriers or a clobbered address. -/
namespace PtxTorchLean.Poisson.PTX.Concurrent.Reduction.Control.Checks

/-- Admitting all 256 lanes to the 128-lane body violates its bound. -/
theorem extra_writers_rejected :
    ¬Limits.Boundaries 256 (program.set 4 (.skip 256 11)) limit := by
  intro h
  have bad := (h.2.1 4 256 11 (by decide +kernel)).1
  change 256≤128 at bad
  omega

/-- Jumping past the first update barrier breaks the required control path. -/
theorem skipped_barrier_rejected :
    ¬StopsAt (program.set 4 (.skip 128 12)) 11 := by
  intro h
  have bad := h 4 128 12 (by decide +kernel) (by omega)
  omega

/-- Moving the sum into the address register loses the prepared-address fact. -/
theorem clobbered_address_rejected :
    AddressHold.tag (program.set 9 (.data (.fp .add 2 (.reg 4) (.reg 5)))) 10=.none := by
  decide +kernel

end PtxTorchLean.Poisson.PTX.Concurrent.Reduction.Control.Checks

import PoissonPTX.IndexedFrames

namespace PtxTorchLean.Poisson.PTX.Indexed

theorem underlying_block (actual : Block (code.map Instr.data) s t) : PTX.Block code s t := by
  induction code generalizing s with
  | nil => cases actual; exact .nil
  | cons op rest ih =>
    cases actual with | cons one tail =>
      cases one with | data one => exact .cons one (ih tail)

end PtxTorchLean.Poisson.PTX.Indexed

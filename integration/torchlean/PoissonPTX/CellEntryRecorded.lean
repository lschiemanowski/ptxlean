import PoissonPTX.CellEntryExists
import PoissonPTX.ByteHistoryFrame

namespace PtxTorchLean.Poisson.PTX.CellEntry

theorem recorded_prefix (run : Runs cfg ctx (program width cells source) s events indices final)
    (words : Words (memory .global) events) : Concurrent.ByteHistory.Recorded memory events := by
  apply Concurrent.ByteHistory.reads_recorded
  intro r reader a found read
  have member := List.mem_of_getElem? found
  have global := read_global run member read
  rw [global,Concurrent.ByteHistory.publish_readonly (events.take r) memory
    (by intro owner wa inPrefix; exact no_global_store run (List.mem_of_mem_take inPrefix))]
  exact words reader a member read global

end PtxTorchLean.Poisson.PTX.CellEntry

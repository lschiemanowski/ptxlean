import PoissonPTX.AssemblyTableCheck
import PoissonPTX.AssemblyOperator
import PoissonPTX.AssemblyArenaChecks

namespace PtxTorchLean.Poisson.PTX.Assembly.TableChecks
open ArenaChecks
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

theorem input_checked : arena.checkRows memory [[0,1],[2]]=true := by decide +kernel

theorem input_represented : arena.RowsEncoded memory [[0,1],[2]] := arena.checkRows_sound input_checked

/-- Swapping two valid indices changes the rounded order; table validation
rejects it even though every access would remain inside the allocation. -/
theorem wrong_order_rejected : arena.checkRows memory [[1,0],[2]]=false := by decide +kernel

theorem corrupt_offset_rejected :
    arena.checkRows (write32 memory 4164 3) [[0,1],[2]]=false := by decide +kernel

theorem corrupt_index_rejected :
    arena.checkRows (write32 memory 4100 3) [[0,1],[2]]=false := by decide +kernel

theorem empty_rows : CompressedRows.offset [[],[4,2,4],[],[1]] 2=3 ∧
    ((List.range' (CompressedRows.offset [[],[4,2,4],[],[1]] 1)
      (CompressedRows.offset [[],[4,2,4],[],[1]] 2-CompressedRows.offset [[],[4,2,4],[],[1]] 1)).map
      (fun k => [[],[4,2,4],[],[1]].flatten[k]?.getD 0))=[4,2,4] := by
  constructor
  · decide +kernel
  · exact CompressedRows.reconstruct _ 1 (by decide)

theorem host_scan : Rows.scan [(0,0),(1,1),(0,2),(1,3),(0,4)] 0=[0,2,4] := by
  rw [Rows.scan_selected]
  decide +kernel

end PtxTorchLean.Poisson.PTX.Assembly.TableChecks

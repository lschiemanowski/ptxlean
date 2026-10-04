import PoissonPTX.CellWitnessAllocation

namespace PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.Witness
open CellMiddle Symbolic

/-- Construct an actual local arithmetic block, choosing each read from the
byte view accumulated from preceding real stores. Address certificates, rather
than desired read values, establish that each instruction can execute. -/
theorem block_exists (code : List Op) (s : PTX.State) (memory : Space → Memory)
    (bounds : AccessBounds width) (thread : Fin n) (active : thread.val<width*width)
    (physical : Allocation width bases s)
    (related : Matches bases (fun _ _ => 0)
      (atPC .addresses (program width) (Numeric.seed width thread.val) s.pc) s)
    (fetch : ∀ j op, code[j]?=some op → (program width)[s.pc+j]?=some (.data op)) :
    ∃ final accesses, Local.Block code s accesses final ∧
      ByteHistory.Recorded memory (accesses.map (Event.data thread)) ∧
      Allocation width bases final ∧
      Matches bases (fun _ _ => 0)
        (atPC .addresses (program width) (Numeric.seed width thread.val) final.pc) final := by
  induction code generalizing s memory with
  | nil => exact ⟨s,[],.nil,.nil,physical,related⟩
  | cons op rest ih =>
    have fetched : (program width)[s.pc]?=some (.data op) := by simpa using fetch 0 op (by simp)
    obtain ⟨next,access,step,values⟩ := ByteHistory.data_exists op s memory (next_valid bounds active physical related fetched)
    have ready : Matches bases (fun _ _ => 0)
        (atPC .addresses (program width) (Numeric.seed width thread.val) next.pc) next := by
      rw [data_pc step,at_next fetched]
      exact update_sound step related (by intro impossible; cases impossible)
    have laterFetch : ∀ j item, rest[j]?=some item → (program width)[next.pc+j]?=some (.data item) := by
      intro j item found
      have earlier := fetch (j+1) item (by simpa using found)
      simpa only [data_pc step,Nat.add_assoc,Nat.add_comm 1 j] using earlier
    obtain ⟨final,accesses,run,recorded,finalPhysical,finalReady⟩ :=
      ih next (ByteHistory.publish memory (access.toList.map (Event.data thread)))
        (allocation_data step physical) ready laterFetch
    refine ⟨final,access.toList++accesses,.cons step run,?_,finalPhysical,finalReady⟩
    rw [List.map_append]
    exact ByteHistory.recorded_append (ByteHistory.data_recorded values thread) recorded

end PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.Witness

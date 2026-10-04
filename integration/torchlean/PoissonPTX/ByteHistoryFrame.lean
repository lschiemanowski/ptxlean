import PoissonPTX.ByteHistoryReads

namespace PtxTorchLean.Poisson.PTX.Concurrent.ByteHistory

variable {space : Space}

theorem publish_readonly (events : List (Event n)) (memory : Space → Memory)
    (noWrites : ∀ owner a, Event.data owner a∈events → a.data.store=true → a.space≠space) :
    publish memory events space=memory space := by
  induction events generalizing memory with
  | nil => rfl
  | cons e rest ih =>
    rw [publish,ih (applyEvent memory e) (by intro owner a member; exact noWrites owner a (List.mem_cons_of_mem _ member))]
    cases e with
    | barrier => rfl
    | data owner a =>
      by_cases write : a.data.store=true
      · have apart := noWrites owner a (by simp) write
        simp [applyEvent,write,Function.update_of_ne (Ne.symm apart)]
      · simp [applyEvent,write]

theorem reads_recorded (reads : Reads memory events) : Recorded memory events := by
  induction events generalizing memory with
  | nil => exact .nil
  | cons e rest ih =>
    refine .cons ?_ (ih ?_)
    · cases e with
      | barrier => trivial
      | data owner a => exact reads 0 owner a rfl
    · intro r reader a found read
      have value := reads (r+1) reader a (by simpa using found) read
      simpa only [List.take_succ_cons,publish] using value

end PtxTorchLean.Poisson.PTX.Concurrent.ByteHistory

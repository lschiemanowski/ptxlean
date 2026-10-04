import PoissonPTX.ByteHistoryAdmission

namespace PtxTorchLean.Poisson.PTX.Concurrent.ByteHistory

/-- Local recording of the chosen witness policy, threaded through the byte
view of the actual stores. It does not install this view into thread states. -/
def ReadEvent (memory : Space → Memory) : Event n → Prop
  | .data _ a => a.data.store=false → a.data.value=read64 (memory a.space) a.data.address
  | .barrier _ => True

inductive Recorded : (Space → Memory) → List (Event n) → Prop
  | nil : Recorded memory []
  | cons : ReadEvent memory e → Recorded (applyEvent memory e) rest → Recorded memory (e::rest)

theorem recorded_reads (recorded : Recorded memory events) : Reads memory events := by
  intro r reader a found read
  induction recorded generalizing r with
  | nil => simp at found
  | cons first rest ih =>
    cases r with
    | zero =>
      simp only [List.getElem?_cons_zero,Option.some.injEq] at found
      subst_vars
      exact first read
    | succ r =>
      have value := ih r (by simpa using found)
      simpa only [List.take_succ_cons,publish] using value

theorem recorded_append (first : Recorded memory before)
    (last : Recorded (publish memory before) after) : Recorded memory (before++after) := by
  induction first with
  | nil => exact last
  | cons one rest ih => exact .cons one (ih last)

theorem read_event_of_values {event : Event n}
    (values : ∀ owner a, event=.data owner a → a.data.store=false → a.data.value=read64 (memory a.space) a.data.address) :
    ReadEvent memory event := by
  cases event with
  | barrier => trivial
  | data owner a => exact values owner a rfl

theorem recorded_admitted (recorded : Recorded memory events) :
    Visibility.Compatible memory events (sources events) ∧ Visibility.Performed events (sources events) :=
  admitted (recorded_reads recorded)

end PtxTorchLean.Poisson.PTX.Concurrent.ByteHistory

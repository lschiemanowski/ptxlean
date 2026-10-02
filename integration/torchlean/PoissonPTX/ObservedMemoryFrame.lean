import PoissonPTX.ControlFlowObserved

namespace PtxTorchLean.Poisson.PTX.Flow.Observed
set_option maxHeartbeats 1000000

/-- The local byte memory still agrees with the initial snapshot at every
recorded read. This is an invariant proved across disjoint stores. -/
def ReadFrame (initial : Space → Memory) (words : List Concurrent.Access)
    (indices : List IndexSources.Access) (s : PTX.State) : Prop :=
  (∀ a∈words, a.data.store=false → read64 (s.memory a.space) a.data.address=read64 (initial a.space) a.data.address) ∧
  (∀ a∈indices, read32 s.global a.address=read32 (initial .global) a.address)

/-- Physical separation of actual recorded accesses, rather than an assumption
about which numerical result a load is supposed to return. -/
def Separate (words : List Concurrent.Access) (indices : List IndexSources.Access) : Prop :=
  (∀ w∈words, w.data.store=true → ∀ r∈words, r.data.store=false → w.space=r.space →
    w.data.address+8≤r.data.address ∨ r.data.address+8≤w.data.address) ∧
  (∀ w∈words, w.data.store=true → w.space=.global → ∀ r∈indices,
    w.data.address+8≤r.address ∨ r.address+4≤w.data.address)

theorem put_frame {address : Nat} {sp : Space} {value : Word} (frame : ReadFrame initial words indices s)
    (wordApart : ∀ a∈words, a.data.store=false → sp=a.space → address+8≤a.data.address ∨ a.data.address+8≤address)
    (indexApart : sp=.global → ∀ a∈indices, address+8≤a.address ∨ a.address+4≤address) :
    ReadFrame initial words indices (put s sp address value) := by
  constructor
  · intro a member read
    have old := frame.1 a member read
    cases sp <;> cases space : a.space <;> simp only [space,PTX.State.memory,put] at old ⊢
    · rw [read64_write64_disjoint _ _ _ _ (wordApart a member read space.symm),old]
    · exact old
    · exact old
    · rw [read64_write64_disjoint _ _ _ _ (wordApart a member read space.symm),old]
  · intro a member
    cases sp with
    | global =>
      change read32 (write64 s.global address value) a.address=_
      rw [read32_write64_disjoint _ _ _ _ (indexApart rfl a member)]
      exact frame.2 a member
    | shared => exact frame.2 a member

theorem data_frame (step : Indexed.Candidate.Data op s t access index)
    (frame : ReadFrame initial words indices s) (apart : Separate words indices)
    (recorded : ∀ a, access=some a → a∈words) : ReadFrame initial words indices t := by
  cases step with
  | data one =>
    cases one with
    | ordinary plain execution =>
      cases execution <;> simp_all [Concurrent.ordinary]
      all_goals exact frame
    | load => exact frame
    | @store sp addr src s valid =>
      apply put_frame frame
      · intro a member read same
        exact apart.1 _ (recorded _ rfl) rfl a member read same
      · intro global a member
        exact apart.2 _ (recorded _ rfl) rfl global a member
  | mad32 => exact frame
  | wide4 => exact frame
  | load32 => exact frame

/-- Control changes only registers, predicates, halt status and instruction
position. It cannot disturb any memory-read frame. -/
theorem simple_frame (frame : ReadFrame initial words indices s.core) :
    ReadFrame initial words indices (simple ctx op s).core := by
  cases op <;> simp only [simple]
  all_goals first | exact frame | (split <;> exact frame)

theorem step_frame (step : Step ctx program s t access index)
    (frame : ReadFrame initial words indices s.core) (apart : Separate words indices)
    (recorded : ∀ a, access=some a → a∈words) : ReadFrame initial words indices t.core := by
  obtain ⟨_,_,_,execution⟩ := step
  cases execution with
  | data one => exact data_frame one frame apart recorded
  | simple => exact simple_frame frame

end PtxTorchLean.Poisson.PTX.Flow.Observed

import PoissonPTX.ObservedMemoryFrame

namespace PtxTorchLean.Poisson.PTX.Flow.Observed

/-- Justified candidate read bits and disjoint writes recover the complete
snapshot execution, including loops and its actual stores. -/
theorem replay (run : Runs ctx program s words indices t)
    (wordValues : ∀ a∈words, a.data.store=false → a.data.value=read64 (initial a.space) a.data.address)
    (indexValues : ∀ a∈indices, a.value=read32 (initial .global) a.address)
    (apart : Separate words indices) (frame : ReadFrame initial words indices s.core) :
    Flow.Runs ctx program s t := by
  induction run with
  | nil => exact .nil
  | @cons s middle access index words indices t step rest ih =>
    have recorded : ∀ a, access=some a → a∈access.toList++words := by intro a eq; simp [eq]
    have recordedIndex : ∀ a, index=some a → a∈index.toList++indices := by intro a eq; simp [eq]
    have one := replay_step step
      (fun a eq read => (wordValues a (recorded a eq) read).trans (frame.1 a (recorded a eq) read).symm)
      (fun a eq => (indexValues a (recordedIndex a eq)).trans (frame.2 a (recordedIndex a eq)).symm)
    have nextFrame := step_frame step frame apart recorded
    refine .cons one (ih ?_ ?_ ?_ ?_)
    · intro a member; exact wordValues a (List.mem_append_right _ member)
    · intro a member; exact indexValues a (List.mem_append_right _ member)
    · constructor
      · intro w member store r observed read same
        exact apart.1 w (List.mem_append_right _ member) store r (List.mem_append_right _ observed) read same
      · intro w member store global r observed
        exact apart.2 w (List.mem_append_right _ member) store global r (List.mem_append_right _ observed)
    · exact ⟨fun a member => nextFrame.1 a (List.mem_append_right _ member),
        fun a member => nextFrame.2 a (List.mem_append_right _ member)⟩

def events (words : List Concurrent.Access) : List (Concurrent.Event 1) := words.map (Concurrent.Event.data 0)
def indexEvents (indices : List IndexSources.Access) : List (Fin 1 × IndexSources.Access) := indices.map (0,·)

/-- Read-only follows from separation of actual stores and reads. Byte sources
can name any actual store; separation forces each read byte to initialization. -/
theorem source_values (compatible : Concurrent.Visibility.Compatible initial (events words) wordSource)
    (indexCompatible : IndexSources.Compatible (initial .global) (events words) (indexEvents indices) indexSource)
    (apart : Separate words indices) :
    (∀ a∈words, a.data.store=false → a.data.value=read64 (initial a.space) a.data.address) ∧
    (∀ a∈indices, a.value=read32 (initial .global) a.address) := by
  constructor
  · intro a member read
    have observed : Concurrent.Event.data (0 : Fin 1) a∈events words := List.mem_map.mpr ⟨a,member,rfl⟩
    obtain ⟨r,located⟩ := List.mem_iff_getElem?.mp observed
    apply Concurrent.Visibility.read_only_value compatible located read
    intro w writer wa fetched store same j k
    obtain ⟨entry,belongs,eq⟩ := List.mem_map.mp (List.mem_of_getElem? fetched)
    cases eq
    have disjoint := apart.1 wa belongs store a member read same
    have := j.isLt; have := k.isLt; omega
  · intro a member
    have observed : ((0 : Fin 1),a)∈indexEvents indices := List.mem_map.mpr ⟨a,member,rfl⟩
    obtain ⟨r,located⟩ := List.mem_iff_getElem?.mp observed
    apply IndexSources.read_only_value indexCompatible located
    intro w writer wa fetched store global j k
    obtain ⟨entry,belongs,eq⟩ := List.mem_map.mp (List.mem_of_getElem? fetched)
    cases eq
    have disjoint := apart.2 wa belongs store global a member
    have := j.isLt; have := k.isLt; omega

/-- A reusable whole-run bridge under explicit physical separation. Establishing
that separation from a particular kernel's control flow is a separate theorem;
no output equation or desired load value is assumed here. -/
theorem admitted_replay (run : Runs ctx program s words indices t)
    (compatible : Concurrent.Visibility.Compatible s.core.memory (events words) wordSource)
    (indexCompatible : IndexSources.Compatible s.core.global (events words) (indexEvents indices) indexSource)
    (apart : Separate words indices) : Flow.Runs ctx program s t := by
  have values := source_values compatible indexCompatible apart
  exact replay run values.1 values.2 apart ⟨fun _ _ _ => rfl,fun _ _ => rfl⟩

end PtxTorchLean.Poisson.PTX.Flow.Observed

import PoissonPTX.ConcurrentProjection

namespace PtxTorchLean.Poisson.PTX.Concurrent.GlobalPublication
variable {n : Nat} {address p : Nat} {value : Word} {memory : Memory}
  {event : Event n} {events order : List (Event n)}

/-- Apply only actual global store records. Loads, shared accesses and barrier
records do not write the published global bytes. -/
def applyEvent (memory : Memory) : Event n → Memory
  | .data _ a => if a.space=.global ∧ a.data.store=true then
      write64 memory a.data.address a.data.value else memory
  | .barrier _ => memory

/-- This is a mathematical merge of recorded writes, not a CUDA host-visibility
or complete PTX memory-admission rule. -/
def publish (memory : Memory) : List (Event n) → Memory
  | [] => memory
  | e::rest => publish (applyEvent memory e) rest

def Safe (events : List (Event n)) (address : Nat) (value : Word) : Prop :=
  ∀ owner a, Event.data owner a∈events → a.space=.global → a.data.store=true →
    (a.data.address=address ∧ a.data.value=value) ∨
      (a.data.address+8≤address ∨ address+8≤a.data.address)

def Present (events : List (Event n)) (address : Nat) (value : Word) : Prop :=
  ∃ owner a, Event.data owner a∈events ∧ a.space=.global ∧ a.data.store=true ∧
    a.data.address=address ∧ a.data.value=value

theorem apply_preserves (safe : Safe [event] address value) (word : read64 memory address=value) :
    read64 (applyEvent memory event) address=value := by
  cases event with
  | barrier => exact word
  | data owner a =>
    simp only [applyEvent]
    split
    · rename_i write
      rcases safe owner a (by simp) write.1 write.2 with ⟨addr,val⟩|apart
      · simp [addr,val]
      · rw [read64_write64_disjoint _ _ _ _ apart,word]
    · exact word

theorem preserves (safe : Safe events address value) (word : read64 memory address=value) :
    read64 (publish memory events) address=value := by
  induction events generalizing memory with
  | nil => exact word
  | cons e rest ih =>
    apply ih
    · intro owner a member; exact safe owner a (List.mem_cons_of_mem _ member)
    · apply apply_preserves (word:=word)
      intro owner a member
      have eq := List.mem_singleton.mp member
      exact safe owner a (by simp [eq])

/-- An actual matching store supplies the word, and every other store either
agrees with it or touches disjoint bytes. No initial output value is assumed. -/
theorem word (safe : Safe events address value) (present : Present events address value) :
    read64 (publish memory events) address=value := by
  induction events generalizing memory with
  | nil => obtain ⟨owner,a,member,_⟩ := present; simp at member
  | cons e rest ih =>
    have tailSafe : Safe rest address value := fun owner a member =>
      safe owner a (List.mem_cons_of_mem _ member)
    obtain ⟨owner,a,member,global,store,addr,val⟩ := present
    rcases List.mem_cons.mp member with eq|member
    · subst e
      apply preserves tailSafe
      simp [applyEvent,global,store,addr,val]
    · exact ih tailSafe ⟨owner,a,member,global,store,addr,val⟩

/-- Publication order may differ from execution order, while retaining the
same event occurrences. The output word is unchanged. -/
theorem permuted_word (permutation : order.Perm events)
    (safe : Safe events address value) (present : Present events address value) :
    read64 (publish memory order) address=value := by
  apply word
  · intro owner a member
    exact safe owner a (permutation.mem_iff.mp member)
  · obtain ⟨owner,a,member,rest⟩ := present
    exact ⟨owner,a,permutation.mem_iff.mpr member,rest⟩

theorem outside (outside : ∀ owner a, Event.data owner a∈events → a.space=.global →
    a.data.store=true → p<a.data.address ∨ a.data.address+8≤p) :
    publish memory events p=memory p := by
  induction events generalizing memory with
  | nil => rfl
  | cons e rest ih =>
    rw [publish,ih (fun owner a member => outside owner a (List.mem_cons_of_mem _ member))]
    cases e with
    | barrier => rfl
    | data owner a =>
      simp only [applyEvent]
      split
      · rename_i write
        exact write64_outside _ _ _ _ (outside owner a (by simp) write.1 write.2)
      · rfl

end PtxTorchLean.Poisson.PTX.Concurrent.GlobalPublication

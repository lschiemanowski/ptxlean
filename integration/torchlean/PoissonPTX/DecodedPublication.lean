import PoissonPTX.GlobalPublication

namespace PtxTorchLean.Poisson.PTX.Concurrent.GlobalPublication
variable {n : Nat} {address : Nat} {value : Float} {memory : Memory}
  {event : Event n} {events order : List (Event n)}

/-- Publication may preserve decoded numerical equality without preserving a
particular exceptional-value encoding. Every write remains a full byte record. -/
def NumericSafe (events : List (Event n)) (address : Nat) (value : Float) : Prop :=
  ∀ owner a, Event.data owner a∈events → a.space=.global → a.data.store=true →
    (a.data.address=address ∧ decode a.data.value=value) ∨
      (a.data.address+8≤address ∨ address+8≤a.data.address)

def NumericPresent (events : List (Event n)) (address : Nat) : Prop :=
  ∃ owner a, Event.data owner a∈events ∧ a.space=.global ∧ a.data.store=true ∧ a.data.address=address

theorem numeric_apply_preserves (safe : NumericSafe [event] address value)
    (word : decode (read64 memory address)=value) :
    decode (read64 (applyEvent memory event) address)=value := by
  cases event with
  | barrier => exact word
  | data owner a =>
    simp only [applyEvent]
    split
    · rename_i write
      rcases safe owner a (by simp) write.1 write.2 with ⟨addr,val⟩|apart
      · simpa [addr] using val
      · rw [read64_write64_disjoint _ _ _ _ apart,word]
    · exact word

theorem numeric_preserves (safe : NumericSafe events address value)
    (word : decode (read64 memory address)=value) :
    decode (read64 (publish memory events) address)=value := by
  induction events generalizing memory with
  | nil => exact word
  | cons e rest ih =>
    apply ih
    · intro owner a member; exact safe owner a (List.mem_cons_of_mem _ member)
    · apply numeric_apply_preserves (word:=word)
      intro owner a member
      have eq := List.mem_singleton.mp member
      exact safe owner a (by simp [eq])

/-- At least one actual store is required. Subsequent overlapping stores must
have the same decoded value, while other stores must be byte-disjoint. -/
theorem numeric_word (safe : NumericSafe events address value) (present : NumericPresent events address) :
    decode (read64 (publish memory events) address)=value := by
  induction events generalizing memory with
  | nil => obtain ⟨owner,a,member,_⟩ := present; simp at member
  | cons e rest ih =>
    have tailSafe : NumericSafe rest address value := fun owner a member =>
      safe owner a (List.mem_cons_of_mem _ member)
    obtain ⟨owner,a,member,global,store,addr⟩ := present
    rcases List.mem_cons.mp member with eq|member
    · subst e
      apply numeric_preserves tailSafe
      rcases safe owner a (by simp) global store with ⟨_,val⟩|apart
      · simpa [applyEvent,global,store,addr] using val
      · omega
    · exact ih tailSafe ⟨owner,a,member,global,store,addr⟩

theorem numeric_permuted (permutation : order.Perm events)
    (safe : NumericSafe events address value) (present : NumericPresent events address) :
    decode (read64 (publish memory order) address)=value := by
  apply numeric_word
  · intro owner a member; exact safe owner a (permutation.mem_iff.mp member)
  · obtain ⟨owner,a,member,rest⟩ := present
    exact ⟨owner,a,permutation.mem_iff.mpr member,rest⟩

end PtxTorchLean.Poisson.PTX.Concurrent.GlobalPublication

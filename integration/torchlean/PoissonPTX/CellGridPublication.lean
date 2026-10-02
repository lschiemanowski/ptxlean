import PoissonPTX.CellGrid
import PoissonPTX.GlobalPublication

namespace PtxTorchLean.Poisson.PTX.CellGrid
open Concurrent.GlobalPublication

/-- Publish actual global stores in the chronological grid history. Block tags
remain in the history; only the application of global stores ignores them. -/
def publish (memory : Memory) (events : List (Event count)) : Memory :=
  Concurrent.GlobalPublication.publish memory (events.map Prod.snd)

theorem applyEvent_congr {one two : Memory} {p : Nat} (same : one p=two p) (event : Concurrent.Event n) :
    applyEvent one event p=applyEvent two event p := by
  cases event with
  | barrier => exact same
  | data owner a =>
    simp only [applyEvent]
    split
    · simp only [write64]; split <;> simp_all
    · exact same

/-- Compare a grid history with one block's projection at a byte untouched by
other blocks. Both histories retain the original order of this block's stores. -/
theorem publication_byte (events : List (Event count)) (block : Fin count)
    (one two : Memory) (p : Nat) (same : one p=two p)
    (apart : ∀ other owner access, (other,Concurrent.Event.data owner access)∈events → other≠block →
      access.space=.global → access.data.store=true → p<access.data.address ∨ access.data.address+8≤p) :
    publish one events p=Concurrent.GlobalPublication.publish two (forBlock block events) p := by
  induction events generalizing one two with
  | nil => exact same
  | cons event rest ih =>
    obtain ⟨other,event⟩ := event
    have tailApart : ∀ other owner access, (other,Concurrent.Event.data owner access)∈rest → other≠block →
        access.space=.global → access.data.store=true → p<access.data.address ∨ access.data.address+8≤p :=
      fun other owner access member => apart other owner access (List.mem_cons_of_mem _ member)
    by_cases own : other=block
    · subst other
      simp only [publish,List.map_cons,Concurrent.GlobalPublication.publish,forBlock,List.filterMap_cons,ite_true] at ⊢
      exact ih _ _ (applyEvent_congr same event) tailApart
    · have unchanged : applyEvent one event p=one p := by
        cases event with
        | barrier => rfl
        | data owner access =>
          simp only [applyEvent]
          split
          · rename_i write
            exact write64_outside _ _ _ _ (apart other owner access (by simp) own write.1 write.2)
          · rfl
      simp only [publish,List.map_cons,Concurrent.GlobalPublication.publish,forBlock,List.filterMap_cons,own,ite_false] at ⊢
      exact ih _ _ (unchanged.trans same) tailApart

/-- Word publication follows from byte separation; no atomic whole-word merge
or supplied output value is needed. -/
theorem publication_word (events : List (Event count)) (block : Fin count)
    (memory : Memory) (address : Nat)
    (apart : ∀ other owner access, (other,Concurrent.Event.data owner access)∈events → other≠block →
      access.space=.global → access.data.store=true →
      access.data.address+8≤address ∨ address+8≤access.data.address) :
    read64 (publish memory events) address=
      read64 (Concurrent.GlobalPublication.publish memory (forBlock block events)) address := by
  apply PTX.Sources.word_eq_of_bytes
  intro k
  simp only [PTX.Sources.byte_read64]
  apply publication_byte events block memory memory (address+k.val) rfl
  intro other owner access member different global store
  have disjoint := apart other owner access member different global store
  have bound := k.isLt
  omega

end PtxTorchLean.Poisson.PTX.CellGrid

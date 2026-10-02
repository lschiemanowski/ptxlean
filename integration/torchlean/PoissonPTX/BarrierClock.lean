import PoissonPTX.ConcurrentTail

namespace PtxTorchLean.Poisson.PTX.Concurrent.Clock
open Ptx

/-- An arrival still in the current generation has an actual waiting bit.
Completions always belong to an older generation. -/
def Before (state : Barrier.State n) : Barrier.Event n → Prop
  | .arrival key thread => key.generation<state.generation ∨
      (key.generation=state.generation ∧ state.arrived thread=true)
  | .completion key => key.generation<state.generation

def generation : Barrier.Event n → Nat
  | .arrival key _ | .completion key => key.generation

theorem monotone (cfg : Barrier.Config n) (s : Barrier.State n) (r : Barrier.Request n) :
    s.generation≤(Barrier.step cfg s r).state.generation := by
  unfold Barrier.step
  dsimp only
  split
  · split
    · exact Nat.le_refl _
    · split <;> simp [Barrier.mark,Barrier.reset]
  · exact Nat.le_refl _

variable {n : Nat} {s : Barrier.State n} {event : Barrier.Event n}

theorem carry (before : Before s event) (cfg : Barrier.Config n) (r : Barrier.Request n) :
    Before (Barrier.step cfg s r).state event := by
  unfold Barrier.step
  dsimp only
  split
  · split
    · exact before
    · split
      · cases event <;> simp only [Before,Barrier.reset] at before ⊢ <;> omega
      · cases event with
        | completion key => exact before
        | arrival key thread =>
          rcases before with past | ⟨same,waiting⟩
          · exact Or.inl past
          · exact Or.inr ⟨same,Barrier.mark_monotone s r.thread thread waiting⟩
  · exact before

variable {n : Nat} {cfg : Barrier.Config n} {s : Barrier.State n}
  {r : Barrier.Request n} {event : Barrier.Event n}

theorem emitted (member : event∈(Barrier.step cfg s r).events) :
    generation event=s.generation ∧ Before (Barrier.step cfg s r).state event := by
  unfold Barrier.step at member ⊢
  dsimp only at member ⊢
  split at member
  · rename_i same
    have gen : r.key.generation=s.generation := by
      have h := congrArg Barrier.Key.generation same
      simpa only [Barrier.key] using h
    split at member
    · simp at member
    · rename_i fresh
      split at member
      · rename_i complete
        simp only [same,fresh,complete,↓reduceIte]
        simp only [List.mem_cons,List.not_mem_nil,or_false] at member
        rcases member with rfl|rfl <;> simp [generation,Before,gen,Barrier.reset]
      · rename_i incomplete
        simp only [same,fresh,incomplete,↓reduceIte]
        simp only [List.mem_singleton] at member
        subst event
        exact ⟨gen,Or.inr ⟨gen,by simp [Barrier.mark]⟩⟩
  · simp at member

/-- Reset state means no arrival from its current generation has happened. -/
theorem before_reset (before : Before (Barrier.reset next) event) : generation event<next := by
  cases event <;> simpa [Before,generation,Barrier.reset] using before

end PtxTorchLean.Poisson.PTX.Concurrent.Clock

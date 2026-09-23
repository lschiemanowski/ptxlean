import Ptx.Memory

/-!
A structural projection of completed collective control onto memory ordering.
The caller must derive this certificate from its instruction/control execution;
this module supplies no PTX labels, read values, or memory-validity assumptions.
A phase identity must distinguish CTA, resource, generation and aligned site.
-/
namespace Ptx.CollectiveOrder

/-- Positions may subdivide actual machine steps so arrival, completion and
resumption remain distinct. `Phase` indexes completed uses only. -/
structure Certificate (Memory Participant Phase : Type) where
  owner : Memory → Participant
  participates : Phase → Participant → Prop
  memoryPos : Memory → Nat
  arrivalPos : Phase → Participant → Nat
  completionPos : Phase → Nat
  resumePos : Phase → Participant → Nat
  arrival_before_completion : ∀ p t, participates p t →
    arrivalPos p t < completionPos p
  completion_before_resume : ∀ p t, participates p t →
    completionPos p < resumePos p t

namespace Certificate

variable {Memory Participant Phase : Type}
variable (c : Certificate Memory Participant Phase)

/-- The access belongs to a participant and precedes that participant's arrival. -/
def Before (e : Memory) (p : Phase) (t : Participant) : Prop :=
  c.owner e = t ∧ c.participates p t ∧ c.memoryPos e < c.arrivalPos p t

/-- The access belongs to a participant and follows that participant's release. -/
def After (e : Memory) (p : Phase) (t : Participant) : Prop :=
  c.owner e = t ∧ c.participates p t ∧ c.resumePos p t < c.memoryPos e

/-- No address restriction is imposed on the cross-barrier ordering edge. -/
def cross (a b : Memory) : Prop :=
  ∃ p ta tb, c.Before a p ta ∧ c.After b p tb

end Certificate

/-- Control nodes are split rather than synchronized bidirectionally. -/
inductive Node (Memory Participant Phase : Type) where
  | memory : Memory → Node Memory Participant Phase
  | arrival : Phase → Participant → Node Memory Participant Phase
  | completion : Phase → Node Memory Participant Phase
  | resume : Phase → Participant → Node Memory Participant Phase

namespace Certificate

variable {Memory Participant Phase : Type}
variable (c : Certificate Memory Participant Phase)

/-- Each constructor records one structural part of the completed-phase path. -/
inductive Edge : Node Memory Participant Phase → Node Memory Participant Phase → Prop where
  | before : c.Before e p t → Edge (.memory e) (.arrival p t)
  | arrived : c.participates p t → Edge (.arrival p t) (.completion p)
  | completed : c.participates p t → Edge (.completion p) (.resume p t)
  | after : c.After e p t → Edge (.resume p t) (.memory e)

def rank : Node Memory Participant Phase → Nat
  | .memory e => c.memoryPos e
  | .arrival p t => c.arrivalPos p t
  | .completion p => c.completionPos p
  | .resume p t => c.resumePos p t

theorem edge_increases {a b : Node Memory Participant Phase} (h : c.Edge a b) :
    c.rank a < c.rank b := by
  cases h with
  | before h => exact h.2.2
  | arrived h => exact c.arrival_before_completion _ _ h
  | completed h => exact c.completion_before_resume _ _ h
  | after h => exact h.2.2

theorem path_increases {a b : Node Memory Participant Phase} (h : Path c.Edge a b) :
    c.rank a < c.rank b :=
  Path.rank_increases c.rank (fun _ _ => c.edge_increases) h

theorem split_acyclic (a : Node Memory Participant Phase) : ¬Path c.Edge a a := by
  intro h
  exact Nat.lt_irrefl _ (c.path_increases h)

/-- Every projected edge has an explicit four-edge witness through one phase. -/
theorem cross_path {a b : Memory} (h : c.cross a b) :
    Path c.Edge (.memory a) (.memory b) := by
  obtain ⟨p, ta, tb, before, after⟩ := h
  exact .join (.edge (.before before))
    (.join (.edge (.arrived before.2.1))
      (.join (.edge (.completed after.2.1)) (.edge (.after after))))

theorem cross_increases {a b : Memory} (h : c.cross a b) :
    c.memoryPos a < c.memoryPos b :=
  c.path_increases (c.cross_path h)

/-- Ordinary ordering must share the certificate's control positions. -/
def projected (ordinary : Memory → Memory → Prop) (a b : Memory) : Prop :=
  ordinary a b ∨ c.cross a b

theorem projected_path_increases (ordinary : Memory → Memory → Prop)
    (ordered : ∀ a b, ordinary a b → c.memoryPos a < c.memoryPos b)
    {a b : Memory} (h : Path (c.projected ordinary) a b) :
    c.memoryPos a < c.memoryPos b := by
  apply Path.rank_increases c.memoryPos (fun a b hab => ?_) h
  rcases hab with h | h
  · exact ordered a b h
  · exact c.cross_increases h

theorem projected_acyclic (ordinary : Memory → Memory → Prop)
    (ordered : ∀ a b, ordinary a b → c.memoryPos a < c.memoryPos b)
    (a : Memory) : ¬Path (c.projected ordinary) a a := by
  intro h
  exact Nat.lt_irrefl _ (c.projected_path_increases ordinary ordered h)

end Certificate
end Ptx.CollectiveOrder

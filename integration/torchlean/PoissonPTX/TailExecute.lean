import PoissonPTX.ConcurrentTail
import PoissonPTX.ConcurrentExec

namespace PtxTorchLean.Poisson.PTX.Concurrent.WithTail

/-- The padding is used only to reuse Kernel.step at an absolute PC. The guard
prevents fetching any padding instruction. -/
def tick (cfg : Config n) (ctx : Fin n → Kernel.Context)
    (front : List Instr) (tail : List Kernel.Instr) (choose : Fin n → Nat → Word)
    (thread : Fin n) (s : State n) : Option (Outcome n) := do
  if s.halted thread || s.core.barrier.arrived thread then none else do
    if (s.core.lanes thread).pc<front.length then
      let out ← Concurrent.tick cfg front choose thread s.core
      return ⟨{s with core:=out.state},out.events⟩
    else
      let i ← tail[(s.core.lanes thread).pc-front.length]?
      let next ← Kernel.step (ctx thread) (List.replicate front.length .ret++tail) (lane s thread)
      return ⟨update s thread next,(access i (lane s thread) next).toList.map (Event.data thread)⟩

theorem tick_sound (h : tick cfg ctx front tail choose thread s=some out) :
    Step cfg ctx front tail thread s out := by
  unfold tick at h
  split at h
  · simp at h
  · rename_i flags
    have running : s.halted thread=false := by cases a : s.halted thread <;> simp_all
    have fresh : s.core.barrier.arrived thread=false := by cases a : s.core.barrier.arrived thread <;> simp_all
    split at h
    · cases he : Concurrent.tick cfg front choose thread s.core with
      | none => simp [he] at h
      | some result =>
        simp [he] at h; subst out
        exact .front running (Concurrent.tick_sound he)
    · rename_i past
      cases hf : tail[(s.core.lanes thread).pc-front.length]? with
      | none => simp [hf] at h
      | some i =>
        cases he : Kernel.step (ctx thread) (List.replicate front.length .ret++tail) (lane s thread) with
        | none => simp [hf,he] at h
        | some next =>
          simp [hf,he] at h; subst out
          obtain ⟨_,j,fetch,eval⟩ := Kernel.step_sound he
          have same : j=i := by
            change (List.replicate front.length Kernel.Instr.ret++tail)[(s.core.lanes thread).pc]?=some j at fetch
            rw [List.getElem?_append_right (by simp; omega)] at fetch
            simpa [hf] using fetch.symm
          subst j
          exact .tail running fresh (by omega) hf eval

def execute (cfg : Config n) (ctx : Fin n → Kernel.Context)
    (front : List Instr) (tail : List Kernel.Instr) (choose : Fin n → Nat → Word) :
    List (Fin n) → State n → Option (Outcome n)
  | [],s => some ⟨s,[]⟩
  | t::rest,s => do
    let first ← tick cfg ctx front tail choose t s
    let last ← execute cfg ctx front tail choose rest first.state
    return ⟨last.state,first.events++last.events⟩

theorem execute_sound (h : execute cfg ctx front tail choose schedule s=some out) :
    Runs cfg ctx front tail s out.events out.state := by
  induction schedule generalizing s out with
  | nil => simp only [execute,Option.some.injEq] at h; subst out; exact Runs.nil
  | cons thread rest ih =>
    cases hf : tick cfg ctx front tail choose thread s with
    | none => simp [execute,hf] at h
    | some first =>
      cases hl : execute cfg ctx front tail choose rest first.state with
      | none => simp [execute,hf,hl] at h
      | some last =>
        simp [execute,hf,hl] at h
        subst out
        exact Runs.cons (tick_sound hf) (ih hl)

end PtxTorchLean.Poisson.PTX.Concurrent.WithTail

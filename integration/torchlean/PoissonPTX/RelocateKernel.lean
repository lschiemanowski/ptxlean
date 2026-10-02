import PoissonPTX.RelocateInverse

namespace PtxTorchLean.Poisson.PTX.Relocate

def kernel (offset : Nat) (s : Kernel.State) : Kernel.State :=
  {s with core:=scalar offset s.core}

@[simp] theorem kernel_simple : kernel offset (Kernel.simple ctx i s)=
    Kernel.simple ctx i (kernel offset s) := by
  cases i <;> simp [kernel,Kernel.simple,Kernel.scalar,Kernel.advance,Kernel.halt]
  split <;> simp_all

theorem kernel_eval (step : Kernel.Eval ctx i s t) :
    Kernel.Eval ctx i (kernel offset s) (kernel offset t) := by
  cases step with
  | simple ordinary => simpa using Kernel.Eval.simple (s:=kernel offset s) ordinary
  | data he => exact Kernel.Eval.data (eval he)

theorem kernel_back (step : Kernel.Eval ctx i (kernel offset s) t) :
    ∃ localState, t=kernel offset localState ∧ Kernel.Eval ctx i s localState := by
  cases step with
  | simple ordinary => exact ⟨Kernel.simple ctx i s,(kernel_simple).symm,.simple ordinary⟩
  | data he =>
    obtain ⟨localState,same,he⟩ := eval_back he
    exact ⟨{s with core:=localState},by simp [same,kernel],.data he⟩

def tailState (offset : Nat) (s : Concurrent.WithTail.State n) : Concurrent.WithTail.State n :=
  {s with core:=core offset s.core}

def tailOutcome (offset : Nat) (s : Concurrent.WithTail.Outcome n) : Concurrent.WithTail.Outcome n :=
  ⟨tailState offset s.state,s.events.map (event offset)⟩

@[simp] theorem tail_lane : Concurrent.WithTail.lane (tailState offset s) t=
    kernel offset (Concurrent.WithTail.lane s t) := rfl

@[simp] theorem tail_update : tailState offset (Concurrent.WithTail.update s t next)=
    Concurrent.WithTail.update (tailState offset s) t (kernel offset next) := by
  simp [tailState,Concurrent.WithTail.update,kernel]

@[simp] theorem tail_access : Concurrent.WithTail.access i (kernel offset s) (kernel offset t)=
    (Concurrent.WithTail.access i s t).map (access offset) := by
  cases i <;> simp only [Concurrent.WithTail.access,Option.map_none]
  cases ‹Op› <;> simp [Concurrent.WithTail.access,kernel,access]

theorem tailState_injective : Function.Injective (tailState (n:=n) offset) := by
  intro s t h
  have a : s.core=t.core := core_injective (congrArg Concurrent.WithTail.State.core h)
  have b := congrArg Concurrent.WithTail.State.predicate h
  have c := congrArg Concurrent.WithTail.State.halted h
  cases s; cases t
  simp_all [tailState]

end PtxTorchLean.Poisson.PTX.Relocate

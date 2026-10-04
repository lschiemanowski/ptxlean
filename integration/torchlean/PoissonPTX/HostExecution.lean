import PoissonPTX.HostSchedule

namespace PtxTorchLean.Poisson.PTX.Host

/-- Execute the host schedule while threading one global byte memory through
all kernel launches and status reads. The launch relation is an explicit
parameter here; concrete PTX instances must establish it separately. -/
inductive Execution (launch : Entry → Memory → Memory → Prop) :
    Plan → Memory → List Entry → Report → Memory → Prop where
  | finish : Execution launch (.finish report) memory [] report memory
  | launch (actual : launch entry memory middle)
      (rest : Execution launch next middle trace report final) :
      Execution launch (.launch entry next) memory (entry::trace) report final
  | inspect (rest : Execution launch (next memory) memory trace report final) :
      Execution launch (.inspect next) memory trace report final

/-- A uniform bound on requested kernel launches, independent of the bytes
observed by every host branch. It does not assert that a kernel returns. -/
inductive Budget : Nat → Plan → Prop where
  | finish : Budget k (.finish report)
  | launch : Budget k next → Budget (k+1) (.launch entry next)
  | inspect : (∀ memory, Budget k (next memory)) → Budget k (.inspect next)

variable {launch : Entry → Memory → Memory → Prop}

theorem Budget.weaken (bounded : Budget k plan) (larger : k≤m) : Budget m plan := by
  induction bounded generalizing m with
  | finish => exact .finish
  | launch next ih =>
    obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m≠0)
    exact .launch (ih (by omega))
  | inspect branches ih => exact .inspect (fun memory => ih memory larger)

theorem launches_budget (bounded : Budget k next) : Budget (entries.length+k) (launches entries next) := by
  induction entries with
  | nil => simpa [launches] using bounded
  | cons entry rest ih => simpa [launches,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using Budget.launch (entry:=entry) ih

/-- A completed execution cannot request more launches than its branch-uniform
budget, even when each launch has many permitted outcomes. -/
theorem Execution.launch_bound (actual : Execution launch plan memory trace report final)
    (bounded : Budget k plan) : trace.length≤k := by
  induction actual generalizing k with
  | finish => simp
  | launch step rest ih => cases bounded with | launch bound => simpa using Nat.succ_le_succ (ih bound)
  | inspect rest ih => cases bounded with | inspect branches => exact ih (branches _)

/-- Host execution exists when actual kernel executions are available and
preserve the given input-storage invariant. This modular lemma deliberately
exposes both obligations; it is not the complete solver existence theorem. -/
theorem Budget.execution_exists (bounded : Budget k plan)
    (valid : Memory → Prop)
    (kernels : ∀ entry memory, valid memory → ∃ next, launch entry memory next ∧ valid next)
    (initial : valid memory) :
    ∃ trace report final, Execution launch plan memory trace report final ∧ valid final := by
  induction bounded generalizing memory with
  | finish => exact ⟨[],_,memory,.finish,initial⟩
  | @launch k next entry bound ih =>
    obtain ⟨middle,actual,ok⟩ := kernels entry memory initial
    obtain ⟨trace,report,final,run,last⟩ := ih ok
    exact ⟨entry::trace,report,final,.launch actual run,last⟩
  | inspect branches ih =>
    obtain ⟨trace,report,final,run,last⟩ := ih memory initial
    exact ⟨trace,report,final,.inspect run,last⟩

end PtxTorchLean.Poisson.PTX.Host

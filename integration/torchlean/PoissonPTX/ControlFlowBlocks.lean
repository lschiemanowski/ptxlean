import PoissonPTX.ControlFlow

namespace PtxTorchLean.Poisson.PTX.Flow

/-- Step counts are proof bookkeeping derived from a run, never a supplied
iteration count or a limit on permitted executions. -/
inductive Counted (ctx : Kernel.Context) (program : List Instr) : Nat → State → State → Prop where
  | nil : Counted ctx program 0 s s
  | cons : Step ctx program s t → Counted ctx program k t u → Counted ctx program (k+1) s u

theorem counted (run : Runs ctx program s t) : ∃ k, Counted ctx program k s t := by
  induction run with
  | nil => exact ⟨0,.nil⟩
  | cons step rest ih => obtain ⟨k,h⟩ := ih; exact ⟨k+1,.cons step h⟩

theorem counted_run (run : Counted ctx program k s t) : Runs ctx program s t := by
  induction run with
  | nil => exact .nil
  | cons step rest ih => exact .cons step ih

theorem peel (run : Counted ctx program k s t) (running : s.halted=false) (done : t.halted=true)
    (fetch : program[s.core.pc]?=some i) :
    ∃ remaining mid, k=remaining+1 ∧ Eval ctx i s mid ∧ Counted ctx program remaining mid t := by
  cases run with
  | nil => simp_all
  | cons next tail =>
    obtain ⟨_,actual,seen,one⟩ := next
    have eq := Option.some.inj (fetch.symm.trans seen)
    subst actual
    exact ⟨_,_,rfl,one,tail⟩

theorem peel_simple (run : Counted ctx program k s t) (running : s.halted=false) (done : t.halted=true)
    (fetch : program[s.core.pc]?=some i) (ordinary : ∀ op, i≠.data op) :
    ∃ remaining, k=remaining+1 ∧ Counted ctx program remaining (simple ctx i s) t := by
  obtain ⟨remaining,mid,number,one,rest⟩ := peel run running done fetch
  cases one with
  | data => exact False.elim (ordinary _ rfl)
  | simple => exact ⟨remaining,number,rest⟩

/-- Recover every fetched instruction in a straight data region preceding the
return, even when the whole program later jumps backwards. -/
theorem peel_block (code : List Indexed.Instr) (pre post : List Instr)
    (run : Counted ctx (pre++code.map Instr.data++post) k s t)
    (pc : s.core.pc=pre.length) (running : s.halted=false) (done : t.halted=true) :
    ∃ remaining core, k=code.length+remaining ∧ Indexed.Block code s.core core ∧
      Counted ctx (pre++code.map Instr.data++post) remaining {s with core:=core} t := by
  induction code generalizing pre k s with
  | nil => exact ⟨k,s.core,by simp,.nil,run⟩
  | cons op code ih =>
    obtain ⟨steps,mid,number,one,rest⟩ := peel run running done (i:=.data op) (by simp [pc])
    cases one with
    | simple ordinary => exact False.elim (ordinary op rfl)
    | data step =>
      rename_i middle
      obtain ⟨remaining,core,length,block,last⟩ := ih (s:={s with core:=middle}) (pre++[Instr.data op])
        (by simpa [List.append_assoc] using rest) (by simpa [pc] using Indexed.eval_pc step) running
      refine ⟨remaining,core,by simp only [List.length_cons]; omega,.cons step block,?_⟩
      simpa [List.append_assoc] using last

/-- A checked data block embeds as ordinary fetched steps, preserving flags. -/
theorem block_run (block : Indexed.Block code s.core t) (running : s.halted=false)
    (pre post : List Instr) (pc : s.core.pc=pre.length) :
    Runs ctx (pre++code.map Instr.data++post) s {s with core:=t} := by
  induction code generalizing pre s with
  | nil => cases block; exact .nil
  | cons op code ih =>
    cases block with
    | cons step rest =>
      apply Runs.cons ⟨running,.data op,by simp [pc],.data step⟩
      simpa [List.append_assoc] using ih (s:={s with core:=_}) rest running (pre++[Instr.data op])
        (by simpa [pc] using Indexed.eval_pc step)

end PtxTorchLean.Poisson.PTX.Flow

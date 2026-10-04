import PoissonPTX.ControlFlowBlocks

namespace PtxTorchLean.Poisson.PTX.Flow.Boundary

/-- A counter boundary can force execution of a fetched instruction without
assuming the entire kernel returns before a later barrier or continuation. -/
theorem peel (run : Counted ctx program k s t) (different : s.core.pc≠t.core.pc)
    (fetch : program[s.core.pc]?=some i) :
    ∃ remaining mid, k=remaining+1 ∧ Eval ctx i s mid ∧ Counted ctx program remaining mid t := by
  cases run with
  | nil => exact False.elim (different rfl)
  | cons next tail =>
    obtain ⟨_,actual,seen,one⟩ := next
    have eq := Option.some.inj (fetch.symm.trans seen)
    subst actual
    exact ⟨_,_,rfl,one,tail⟩

theorem peel_simple (run : Counted ctx program k s t) (different : s.core.pc≠t.core.pc)
    (fetch : program[s.core.pc]?=some i) (ordinary : ∀ op, i≠.data op) :
    ∃ remaining, k=remaining+1 ∧ Counted ctx program remaining (simple ctx i s) t := by
  obtain ⟨remaining,mid,number,one,rest⟩ := peel run different fetch
  cases one with
  | data => exact False.elim (ordinary _ rfl)
  | simple => exact ⟨remaining,number,rest⟩

theorem peel_block (code : List Indexed.Instr) (pre post : List Instr)
    (run : Counted ctx (pre++code.map Instr.data++post) k s t)
    (pc : s.core.pc=pre.length) (past : pre.length+code.length≤t.core.pc) :
    ∃ remaining core, k=code.length+remaining ∧ Indexed.Block code s.core core ∧
      Counted ctx (pre++code.map Instr.data++post) remaining {s with core:=core} t := by
  induction code generalizing pre k s with
  | nil => exact ⟨k,s.core,by simp,.nil,run⟩
  | cons op code ih =>
    obtain ⟨steps,mid,number,one,rest⟩ := peel run (by simp only [List.length_cons] at past; omega)
      (i:=.data op) (by simp [pc])
    cases one with
    | simple ordinary => exact False.elim (ordinary op rfl)
    | data step =>
      rename_i middle
      obtain ⟨remaining,core,length,block,last⟩ := ih (s:={s with core:=middle}) (pre++[Instr.data op])
        (by simpa [List.append_assoc] using rest) (by simpa [pc] using Indexed.eval_pc step)
        (by simpa [Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using past)
      refine ⟨remaining,core,by simp only [List.length_cons]; omega,.cons step block,?_⟩
      simpa [List.append_assoc] using last

end PtxTorchLean.Poisson.PTX.Flow.Boundary

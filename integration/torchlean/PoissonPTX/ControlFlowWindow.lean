import PoissonPTX.ControlFlowBlocks
import PoissonPTX.ControlFlowLoop

namespace PtxTorchLean.Poisson.PTX.Flow.Window

/-- A loop embedded inside an actual entry, with absolute branch targets and
an arbitrary continuation after its real exit label. -/
def header (origin cursor stop : Nat) (body : List Indexed.Instr) : List Instr :=
  [.compare 0 .ge (.reg cursor) (.reg stop),.branch 0 true (origin+body.length+3)]

def program (pre : List Instr) (cursor stop : Nat) (body : List Indexed.Instr) (post : List Instr) : List Instr :=
  pre++header pre.length cursor stop body++body.map Instr.data++[.jump pre.length]++post

inductive Traversal (origin cursor stop : Nat) (body : List Indexed.Instr) : PTX.State → PTX.State → Prop where
  | done (endOfList : Loop.exhausted cursor stop s=true) :
      Traversal origin cursor stop body s {s with pc:=origin+body.length+3}
  | more (inside : Loop.exhausted cursor stop s=false)
      (step : Indexed.Block body {s with pc:=origin+2} middle)
      (rest : Traversal origin cursor stop body {middle with pc:=origin} final) :
      Traversal origin cursor stop body s final

/-- The loop cut is obtained from actual fetched steps. In particular it
retains the real continuation and does not replace the exit with a return. -/
theorem cut (run : Counted ctx (program pre cursor stop body post) k s t)
    (pc : s.core.pc=pre.length) (running : s.halted=false) (done : t.halted=true) :
    ∃ remaining ready, remaining≤k ∧ Traversal pre.length cursor stop body s.core ready.core ∧
      ready.core.pc=pre.length+body.length+3 ∧ ready.halted=false ∧
      Counted ctx (program pre cursor stop body post) remaining ready t := by
  induction k using Nat.strong_induction_on generalizing s with
  | h k ih =>
    obtain ⟨afterCompare,number,compared⟩ := peel_simple run running done
      (i:=.compare 0 .ge (.reg cursor) (.reg stop)) (by simp [program,header,pc]) (by intro op eq; cases eq)
    let comparedState := simple ctx (.compare 0 .ge (.reg cursor) (.reg stop)) s
    obtain ⟨afterBranch,number2,branched⟩ := peel_simple compared running done
      (i:=.branch 0 true (pre.length+body.length+3))
      (by simp [program,header,simple,next,advance,pc,List.getElem?_append_right]) (by intro op eq; cases eq)
    cases decision : Loop.exhausted cursor stop s.core with
    | true =>
      unfold Loop.exhausted at decision
      have branchState : simple ctx (.branch 0 true (pre.length+body.length+3)) comparedState=
          {comparedState with core:={s.core with pc:=pre.length+body.length+3}} := by
        simp [simple,comparedState,next,goto,Operand.eval,decision,advance]
      change Counted _ _ _ (simple ctx (.branch 0 true (pre.length+body.length+3)) comparedState) _ at branched
      rw [branchState] at branched
      exact ⟨afterBranch,{comparedState with core:={s.core with pc:=pre.length+body.length+3}},by omega,.done decision,rfl,running,branched⟩
    | false =>
      unfold Loop.exhausted at decision
      have branchState : simple ctx (.branch 0 true (pre.length+body.length+3)) comparedState=
          {comparedState with core:={s.core with pc:=pre.length+2}} := by
        simp [simple,comparedState,next,Operand.eval,decision,advance,pc]
      change Counted _ _ _ (simple ctx (.branch 0 true (pre.length+body.length+3)) comparedState) _ at branched
      rw [branchState] at branched
      obtain ⟨afterBody,core,number3,block,continued⟩ := peel_block (s:={comparedState with core:={s.core with pc:=pre.length+2}}) body (pre++header pre.length cursor stop body)
        ([.jump pre.length]++post) (by simpa [program,List.append_assoc] using branched)
        (by simp [header]) running done
      have bodyPC : core.pc=pre.length+body.length+2 := by have := Indexed.block_pc block; simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using this
      obtain ⟨afterJump,number4,jumped⟩ := peel_simple (s:={comparedState with core:=core}) continued running done (i:=.jump pre.length)
        (by simp [header,bodyPC,List.getElem?_append_right,Nat.add_assoc]) (by intro op eq; cases eq)
      have smaller : afterJump<k := by omega
      obtain ⟨remaining,ready,bound,trace,exit,runs,rest⟩ := ih afterJump smaller (s:=simple ctx (.jump pre.length) {comparedState with core:=core})
        (by simpa [program,List.append_assoc] using jumped) (by rfl) running
      exact ⟨remaining,ready,by omega,.more decision block trace,exit,runs,rest⟩

theorem exit_pc (trace : Traversal origin cursor stop body s t) : t.pc=origin+body.length+3 := by
  induction trace with
  | done => rfl
  | more _ _ _ ih => exact ih

end PtxTorchLean.Poisson.PTX.Flow.Window

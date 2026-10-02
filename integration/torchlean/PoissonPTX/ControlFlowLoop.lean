import PoissonPTX.ControlFlowBlocks

namespace PtxTorchLean.Poisson.PTX.Flow.Loop

def header (cursor stop : Nat) (body : List Indexed.Instr) : List Instr :=
  [.compare 0 .ge (.reg cursor) (.reg stop),.branch 0 true (body.length+3)]

def program (cursor stop : Nat) (body : List Indexed.Instr) : List Instr :=
  header cursor stop body++body.map Instr.data++[.jump 0,.ret]

def exhausted (cursor stop : Nat) (s : PTX.State) : Bool :=
  Compare.ge.apply (s.regs cursor) (s.regs stop)

/-- A structured account extracted from the fetched loop. Each iteration still
contains the actual byte-addressed instruction block, with all safety checks. -/
inductive Traversal (cursor stop : Nat) (body : List Indexed.Instr) : PTX.State → PTX.State → Prop where
  | done (endOfList : exhausted cursor stop s=true) :
      Traversal cursor stop body s {s with pc:=body.length+4}
  | more (inside : exhausted cursor stop s=false)
      (step : Indexed.Block body {s with pc:=2} middle)
      (rest : Traversal cursor stop body {middle with pc:=0} final) :
      Traversal cursor stop body s final

theorem halted_eq (run : Counted ctx code k s t) (done : s.halted=true) : t=s := by
  cases run with
  | nil => rfl
  | cons step rest => exact False.elim (halted_no_step done step)

/-- Recover loop traversal from every completed fetched execution, without
assuming the branch outcomes, iteration count, load values or loop result. -/
theorem counted_traversal (run : Counted ctx (program cursor stop body) k s t)
    (pc : s.core.pc=0) (running : s.halted=false) (done : t.halted=true) :
    Traversal cursor stop body s.core t.core := by
  induction k using Nat.strong_induction_on generalizing s with
  | h k ih =>
    obtain ⟨afterCompare,number,compared⟩ := peel_simple run running done
      (i:=.compare 0 .ge (.reg cursor) (.reg stop)) (by simp [program,header,pc]) (by intro op eq; cases eq)
    let comparedState := simple ctx (.compare 0 .ge (.reg cursor) (.reg stop)) s
    have pc1 : comparedState.core.pc=1 := by simp [comparedState,simple,next,advance,pc]
    obtain ⟨afterBranch,number2,branched⟩ := peel_simple compared running done
      (i:=.branch 0 true (body.length+3)) (by simp [program,header,simple,next,advance,pc]) (by intro op eq; cases eq)
    cases decision : exhausted cursor stop s.core with
    | true =>
      unfold exhausted at decision
      have branchState : simple ctx (.branch 0 true (body.length+3)) comparedState=
          {comparedState with core:={s.core with pc:=body.length+3}} := by
        simp [simple,comparedState,next,goto,Operand.eval,decision,advance]
      change Counted _ _ _ (simple ctx (.branch 0 true (body.length+3)) comparedState) _ at branched
      rw [branchState] at branched
      obtain ⟨afterRet,number3,returned⟩ := peel_simple branched running done
        (i:=.ret) (by simp [program,header,List.getElem?_append_right]) (by intro op eq; cases eq)
      have same := halted_eq returned (by rfl)
      rw [same]
      simpa [simple,halt,next,advance] using Traversal.done (body:=body) decision
    | false =>
      unfold exhausted at decision
      have branchState : simple ctx (.branch 0 true (body.length+3)) comparedState=
          {comparedState with core:={s.core with pc:=2}} := by
        simp [simple,comparedState,next,goto,Operand.eval,decision,advance,advance,pc]
      change Counted _ _ _ (simple ctx (.branch 0 true (body.length+3)) comparedState) _ at branched
      rw [branchState] at branched
      obtain ⟨afterBody,core,number3,block,continued⟩ := peel_block body (header cursor stop body) [.jump 0,.ret]
        branched (by rfl) running done
      have bodyPC : core.pc=body.length+2 := by have := Indexed.block_pc block; simpa [Nat.add_comm] using this
      obtain ⟨afterJump,number4,jumped⟩ := peel_simple continued running done (i:=.jump 0)
        (by simp [program,header,bodyPC,List.getElem?_append_right]) (by intro op eq; cases eq)
      have smaller : afterJump<k := by omega
      have result := ih afterJump smaller jumped (by rfl) running
      exact .more decision block result

theorem traversal (run : Runs ctx (program cursor stop body) s t)
    (pc : s.core.pc=0) (running : s.halted=false) (done : t.halted=true) :
    Traversal cursor stop body s.core t.core := by
  obtain ⟨k,count⟩ := counted run
  exact counted_traversal count pc running done

end PtxTorchLean.Poisson.PTX.Flow.Loop

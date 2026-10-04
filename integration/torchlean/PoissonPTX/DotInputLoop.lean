import PoissonPTX.DotInputExists

namespace PtxTorchLean.Poisson.PTX.DotInput

/-- The emitted loop, ending at its exit boundary (no artificial return).
The initial accumulator and cursor belong to the preceding setup instructions. -/
def program (count : Nat) (left right : Word) : List Flow.Instr :=
  Flow.OperandWindow.program [] 12 (.imm (BitVec.ofNat 64 count))
    ((body left right).map Indexed.Instr.data) []

theorem program_length : (program count left right).length=14 := by
  simp [program,Flow.OperandWindow.program,Flow.OperandWindow.header,body,loadCode,addressCode]

theorem no_continuation (run : Flow.Counted ctx code steps s t)
    (noFetch : code[s.core.pc]?=none) : t=s := by
  cases run with
  | nil => rfl
  | cons first rest =>
    obtain ⟨_,i,fetch,_⟩ := first
    rw [noFetch] at fetch
    cases fetch

theorem correct_loop (run : Flow.Runs ctx (program count left right) s t)
    (pc : s.core.pc=0) (running : s.halted=false) (done : t.core.pc=14)
    (bounded : count<2^30)
    (safe : ∀ index<count, Valid (atCursor s.core index) left right) :
    decode (t.core.regs 8)=(indices count (cursor s.core)).foldl
      (fun acc index => acc+contribution s.core left right index) (decode (s.core.regs 8)) ∧
    Stable s.core t.core := by
  obtain ⟨steps,actual⟩ := Flow.counted run
  obtain ⟨remaining,ready,_,traverse,exit,_,rest⟩ := Flow.OperandWindow.cut actual pc running
    (by simp [done,body,loadCode,addressCode])
  have readyPC : ready.core.pc=14 := by simpa [body,loadCode,addressCode] using exit
  have finalEq := no_continuation rest (by change (program count left right)[ready.core.pc]?=none; rw [readyPC,← program_length (count:=count) (left:=left) (right:=right)]; simp)
  rw [finalEq]
  exact traversal_correct traverse bounded (stable_refl _) safe

theorem exists_loop (s : Flow.State) (pc : s.core.pc=0) (running : s.halted=false)
    (bounded : count<2^30)
    (safe : ∀ index<count, Valid (atCursor s.core index) left right) :
    ∃ t, Flow.Runs ctx (program count left right) s t ∧ t.core.pc=14 ∧ t.halted=false ∧
      decode (t.core.regs 8)=(indices count (cursor s.core)).foldl
        (fun acc index => acc+contribution s.core left right index) (decode (s.core.regs 8)) := by
  obtain ⟨core,traverse⟩ := traversal_exists (origin:=0) s.core bounded (stable_refl _) safe
  obtain ⟨t,actual,same,running⟩ := Flow.OperandWindow.traversal_runs (pre:=[]) (post:=[])
    (ctx:=ctx) traverse s rfl pc running
  have exit : t.core.pc=14 := by
    rw [same,Flow.OperandWindow.exit_pc traverse]
    simp [body,loadCode,addressCode]
  exact ⟨t,actual,exit,running,(correct_loop actual pc (by assumption) exit bounded safe).1⟩

end PtxTorchLean.Poisson.PTX.DotInput

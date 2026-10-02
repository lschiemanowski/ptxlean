import PoissonPTX.CellEntryResult
import PoissonPTX.CellEntryBarrier

namespace PtxTorchLean.Poisson.PTX.CellEntry
variable {n : Nat} {s t : State n} {out : Outcome n} {cfg : Concurrent.Config n}
  {ctx : Fin n → CellPrologue.Context}

theorem store_instruction {pc : Nat} {address value : Operand}
    (fetch : (program width cells source)[pc]?=some (.gather (.data (.store64 sp address value)))) :
    pc=19 ∧ sp=.shared ∧ address=.offset 2 0 ∧ value=.reg 11 := by
  have bound := (List.getElem?_eq_some_iff.mp fetch).1
  rw [program_length] at bound
  interval_cases pc <;> simp_all [program,CellPrologue.program,CellGather.code]

/-- Inspect the actual emitted record and fetched store operands. -/
theorem store_origin (step : Step cfg ctx (program width cells source) selected s out)
    (member : Concurrent.Event.data owner access∈out.events) (store : access.data.store=true) :
    selected=owner ∧ (s.core.lanes owner).pc=19 ∧ access.space=.shared ∧
    access.data.pc=19 ∧ access.data.address=((s.core.lanes owner).regs 2).toNat ∧
    access.data.value=(s.core.lanes owner).regs 11 ∧
    (out.state.core.lanes owner).pc=20 ∧
    (out.state.core.lanes owner).shared=write64 (s.core.lanes owner).shared access.data.address access.data.value ∧
    (out.state.core.lanes owner).regs=(s.core.lanes owner).regs := by
  obtain ⟨fresh,i,fetch,dispatch⟩ := step
  cases dispatch with
  | setup => simp at member
  | skip => simp at member
  | gather hd =>
    have same : ‹Option Concurrent.Access›=some access ∧ selected=owner := by simpa using member
    rcases same with ⟨same,rfl⟩
    rw [same] at hd
    cases hd with
    | data he => cases he with
      | load => simp at store
      | store valid =>
        obtain ⟨pc,rfl,rfl,rfl⟩ := store_instruction fetch
        simp [pc,Concurrent.setLane,put,advance,Operand.eval]
  | sync =>
    simp only [synchronize,Concurrent.synchronize] at member
    split at member <;> simp_all

/-- All lane data apart from the instruction counter. -/
def contents (s : PTX.State) : PTX.State := {s with pc:=0}

/-- After the store, this prefix can only wait at the barrier or finish. -/
theorem step_after_store (step : Step cfg ctx (program width cells source) selected s out)
    (owner : Fin n) (past : 20≤(s.core.lanes owner).pc) :
    20≤(out.state.core.lanes owner).pc ∧
    contents (out.state.core.lanes owner)=contents (s.core.lanes owner) := by
  obtain ⟨fresh,i,fetch,dispatch⟩ := step
  have bound := (List.getElem?_eq_some_iff.mp fetch).1
  rw [program_length] at bound
  cases dispatch with
  | setup =>
    by_cases same : owner=selected
    · subst owner
      have here : (s.core.lanes selected).pc=20 := by omega
      rw [here,barrier_fetch] at fetch; cases fetch
    · simp [setLane,Concurrent.setLane,Function.update,same,past]
  | gather =>
    by_cases same : owner=selected
    · subst owner
      have here : (s.core.lanes selected).pc=20 := by omega
      rw [here,barrier_fetch] at fetch; cases fetch
    · simp [Concurrent.setLane,Function.update,same,past]
  | skip =>
    by_cases same : owner=selected
    · subst owner
      have here : (s.core.lanes selected).pc=20 := by omega
      rw [here,barrier_fetch] at fetch; cases fetch
    · simp [Concurrent.setLane,Function.update,same,past]
  | sync =>
    simp only [synchronize,Concurrent.synchronize]
    split
    · exact ⟨past,rfl⟩
    · exact ⟨past,rfl⟩
    · exact ⟨by change 20≤(s.core.lanes owner).pc+1; omega,rfl⟩

theorem runs_after_store (run : Runs cfg ctx (program width cells source) s events indices t)
    (owner : Fin n) (past : 20≤(s.core.lanes owner).pc) :
    20≤(t.core.lanes owner).pc ∧ contents (t.core.lanes owner)=contents (s.core.lanes owner) := by
  induction run with
  | nil => exact ⟨past,rfl⟩
  | cons step _ ih =>
    have first := step_after_store step owner past
    have later := ih first.1
    exact ⟨later.1,later.2.trans first.2⟩

/-- Every store record has the final lane's address register and value register.
This lemma does not assume which lanes wrote or supply their output values. -/
theorem recorded_store (run : Runs cfg ctx (program width cells source) s events indices t)
    (member : Concurrent.Event.data owner access∈events) (store : access.data.store=true) :
    access.space=.shared ∧ access.data.pc=19 ∧
    access.data.address=((t.core.lanes owner).regs 2).toNat ∧
    access.data.value=(t.core.lanes owner).regs 11 ∧
    read64 (t.core.lanes owner).shared access.data.address=access.data.value := by
  induction run with
  | nil => simp at member
  | @cons selected s out rest indices final step tail ih =>
    rcases List.mem_append.mp member with first | later
    · obtain ⟨_,_,shared,pc,address,value,next,bytes,registers⟩ := store_origin step first store
      have frame := (runs_after_store tail owner (by omega)).2
      have regs := congrArg PTX.State.regs frame
      have mem := congrArg PTX.State.shared frame
      change (final.core.lanes owner).regs=(out.state.core.lanes owner).regs at regs
      change (final.core.lanes owner).shared=(out.state.core.lanes owner).shared at mem
      refine ⟨shared,pc,?_,?_,?_⟩
      · rw [regs,registers]; exact address
      · rw [regs,registers]; exact value
      · rw [mem,bytes,read64_write64]
    · exact ih later

end PtxTorchLean.Poisson.PTX.CellEntry

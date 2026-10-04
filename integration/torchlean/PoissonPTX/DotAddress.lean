import PoissonPTX.DotAddressSyntax

namespace PtxTorchLean.Poisson.PTX.Concurrent.Dot

/-- Register facts needed at the actual output address instructions. The base
fact becomes available only after the arena parameter has been loaded. -/
def AddressReady (base output : Word) (s : Flow.State) : Prop :=
  (2≤s.core.pc → s.core.regs 0=base) ∧
  (s.core.pc=100 → s.core.regs 1=0) ∧
  (s.core.pc=101 → s.core.regs 2=base) ∧
  (s.core.pc=102 → s.core.regs 2=base+output)

theorem address_ready_initial (start : s.core.pc=0) : AddressReady base output s := by
  simp [AddressReady,start]

theorem address_ready_early (base : 2≤s.core.pc → s.core.regs 0=arena)
    (early : s.core.pc<100) : AddressReady arena output s := by
  exact ⟨base,by omega,by omega,by omega⟩

theorem input_address
    (fetch : (DotInput.inputProgram count left right scratch)[s.core.pc]?=some i)
    (actual : Flow.Observed.Eval ctx i s t access index)
    (ready : AddressReady ctx.arena output s) : AddressReady ctx.arena output t := by
  have bound : s.core.pc<20 := by
    have h := (List.getElem?_eq_some_iff.mp fetch).1
    simpa only [DotInput.input_length] using h
  have upper := NativeFlow.eval_upper actual bound (input_syntax (List.mem_of_getElem? fetch)).1
  apply address_ready_early (early:=by omega)
  intro later
  by_cases first : s.core.pc=0
  · have op : i=.data (.data (.mov 3 (.imm scratch))) := by
      simpa [first,DotInput.inputProgram,Flow.OperandWindow.program,DotInput.setupCode] using fetch.symm
    subst i
    cases actual with
    | data one =>
      have pc := Indexed.Candidate.data_pc one
      simp only at later
      rw [pc,first] at later
      omega
    | simple ordinary => exact False.elim (ordinary _ rfl)
  · by_cases second : s.core.pc=1
    · have op : i=.context 0 .arena := by
        simpa [second,DotInput.inputProgram,Flow.OperandWindow.program,DotInput.setupCode] using fetch.symm
      subst i
      cases actual
      simp [Flow.simple,Flow.source,assign,advance]
    · rw [NativeFlow.eval_keeps actual (input_keeps_base fetch second)]
      exact ready.1 (by omega)

theorem tree_address
    (before : 20≤s.core.pc) (inside : s.core.pc<96)
    (fetch : (program count left right output scratch)[s.core.pc]?=some (.flow i))
    (actual : Flow.Observed.Eval ctx i s t access index)
    (ready : AddressReady ctx.arena output s) : AddressReady ctx.arena output t := by
  have position : s.core.pc=20+(s.core.pc-20) := by omega
  rw [position,tree_fetch (by omega)] at fetch
  obtain ⟨native,found,ordinary⟩ := Option.map_eq_some_iff.mp fetch
  have checked :=  tree_base found ordinary
  have upper := NativeFlow.eval_upper actual inside checked.2
  apply address_ready_early (early:=by omega)
  intro _
  exact (NativeFlow.eval_keeps actual checked.1).trans (ready.1 (by omega))

end PtxTorchLean.Poisson.PTX.Concurrent.Dot

import PoissonPTX.DotPublicationSyntax
import PoissonPTX.NativeFlowInitialized

namespace PtxTorchLean.Poisson.PTX.Concurrent.Dot

theorem input_keeps_lane (fetch : (DotInput.inputProgram count left right scratch)[pc]?=some i)
    (other : pc≠2) : NativeFlow.keeps 14 i := by
  have small : pc<20 := by
    have := (List.getElem?_eq_some_iff.mp fetch).1
    simpa only [DotInput.input_length] using this
  interval_cases pc <;>
    simp_all [DotInput.inputProgram,Flow.OperandWindow.program,Flow.OperandWindow.header,
      DotInput.setupCode,DotInput.body,loadCode,addressCode]
  all_goals cases fetch; simp [NativeFlow.keeps,Indexed.keeps,SharedStore.keeps]

theorem input_keeps_scratch (fetch : (DotInput.inputProgram count left right scratch)[pc]?=some i)
    (other : pc≠0) : NativeFlow.keeps 3 i := by
  have small : pc<20 := by
    have := (List.getElem?_eq_some_iff.mp fetch).1
    simpa only [DotInput.input_length] using this
  interval_cases pc <;>
    simp_all [DotInput.inputProgram,Flow.OperandWindow.program,Flow.OperandWindow.header,
      DotInput.setupCode,DotInput.body,loadCode,addressCode]
  all_goals cases fetch; simp [NativeFlow.keeps,Indexed.keeps,SharedStore.keeps]

theorem checked_tree_registers : ∀ slot : Fin 76,
    (match Reduction.Native.code[slot.val]? with
    | some (.data op) => AddressHold.keep 3 op && AddressHold.keep 14 op
    | _ => true)=true := by decide +kernel

theorem tree_keeps_setup {pc : Nat} (fetch : Reduction.Native.code[pc]?=some native)
    (ordinary : treeInstruction native=.flow i) : NativeFlow.keeps 3 i ∧ NativeFlow.keeps 14 i := by
  have bound := (List.getElem?_eq_some_iff.mp fetch).1
  rw [Reduction.Native.length] at bound
  have checked := checked_tree_registers ⟨pc,bound⟩
  rw [fetch] at checked
  cases native <;> cases ordinary
  · simp only [Bool.and_eq_true] at checked
    exact ⟨AddressHold.keep_correct.mp checked.1,AddressHold.keep_correct.mp checked.2⟩
  · exact ⟨trivial,trivial⟩
  · exact ⟨trivial,trivial⟩

theorem keeps_setup (fetch : (program count left right output scratch)[pc]?=some (.flow i)) :
    (pc≠0 → NativeFlow.keeps 3 i) ∧ (pc≠2 → NativeFlow.keeps 14 i) := by
  by_cases input : pc<20
  · rw [input_fetch input] at fetch
    obtain ⟨op,found,equal⟩ := Option.map_eq_some_iff.mp fetch
    cases equal
    exact ⟨input_keeps_scratch found,input_keeps_lane found⟩
  · by_cases inside : pc<96
    · have position : pc=20+(pc-20) := by omega
      rw [position,tree_fetch (by omega)] at fetch
      obtain ⟨op,found,equal⟩ := Option.map_eq_some_iff.mp fetch
      have stable := tree_keeps_setup found equal
      exact ⟨fun _ => stable.1,fun _ => stable.2⟩
    · have position : pc=96+(pc-96) := by omega
      rw [position,tail_fetch] at fetch
      obtain ⟨op,found,equal⟩ := Option.map_eq_some_iff.mp fetch
      cases equal
      have member := List.mem_of_getElem? found
      simp only [tail,List.mem_cons,List.not_mem_nil,or_false] at member
      rcases member with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        simp [NativeFlow.keeps,Indexed.keeps,SharedStore.keeps]

def SetupRegisters (ctx : Kernel.Context) (scratch : Word) (s : Flow.State) : Prop :=
  (0<s.core.pc → s.core.regs 3=scratch) ∧
  (2<s.core.pc → s.core.regs 14=ctx.lane.setWidth 64)

theorem setup_registers_flow
    (fetch : (program count left right output scratch)[s.core.pc]?=some (.flow i))
    (actual : Flow.Observed.Eval ctx i s t access index) (ready : SetupRegisters ctx scratch s) :
    SetupRegisters ctx scratch t := by
  constructor
  · apply NativeFlow.initialized_flow actual fetch ready.1
    · intro pc i before; omega
    · intro i s t access index pc found step
      rw [input_fetch (by decide)] at found
      change some (NativeFlow.Instr.flow (.data (.data (.mov 3 (.imm scratch)))))=some (NativeFlow.Instr.flow i) at found
      cases found
      cases step
      · cases_type* Indexed.Candidate.Data Concurrent.Data PTX.Eval
        simp [assign,advance,Operand.eval]
      · rename_i ordinary; exact False.elim (ordinary _ rfl)
    · intro pc i past found; exact (keeps_setup found).1 (by omega)
  · apply NativeFlow.initialized_flow actual fetch ready.2
    · intro pc i before found
      rw [input_fetch (by omega)] at found
      interval_cases pc <;>
        simp [DotInput.inputProgram,Flow.OperandWindow.program,DotInput.setupCode] at found
      all_goals cases found; trivial
    · intro i s t access index pc found step
      rw [input_fetch (by decide)] at found
      change some (NativeFlow.Instr.flow (.context 14 .lane))=some (NativeFlow.Instr.flow i) at found
      cases found
      cases step
      simp [Flow.simple,Flow.source,assign,advance]
    · intro pc i past found; exact (keeps_setup found).2 (by omega)

theorem setup_registers
    (run : NativeFlow.Runs cfg ctx (program count left right output scratch) start events indices final)
    (aligned : Aligned start.core) (entry : ∀ thread, (start.core.lanes thread).pc=0) :
    ∀ owner, SetupRegisters (ctx owner) scratch (NativeFlow.lane final owner) := by
  apply NativeFlow.runs_lanes (P:=fun owner s => SetupRegisters (ctx owner) scratch s) run aligned (fun owner => by simp [SetupRegisters,NativeFlow.lane,entry])
  · intro owner i before after access index ready fetch actual
    exact setup_registers_flow fetch actual ready
  · intro owner before resource ready fetch
    constructor
    · exact NativeFlow.initialized_sync ready.1 fetch (no_early_sync (by decide))
    · exact NativeFlow.initialized_sync ready.2 fetch (no_early_sync (by decide))

end PtxTorchLean.Poisson.PTX.Concurrent.Dot

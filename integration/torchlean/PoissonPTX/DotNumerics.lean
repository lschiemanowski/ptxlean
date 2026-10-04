import PoissonPTX.DotTreeSources
import PoissonPTX.NativeFlowValues
import PoissonPTX.ReductionNumerics

namespace PtxTorchLean.Poisson.PTX.Concurrent.Dot.Numeric
open Concurrent.Values
abbrev values := Reduction.Control.Numeric.values

def loads (input : Nat → Float) (phase : Fin 8) (pc : Nat) : Option (Fin 256 → Float) :=
  if pc=readPC phase false then some (fun t => values input phase.val t.val)
  else if pc=readPC phase true then some (fun t => values input phase.val (t.val+stride phase))
  else none

theorem input_entry_table : NativeFlow.Numeric.tag (program count left right output scratch) loadContract 6=empty := by
  funext r
  simp [NativeFlow.Numeric.tag,NativeFlow.Numeric.transfer,program,DotInput.inputProgram,
    Flow.OperandWindow.program,DotInput.setupCode,Values.transfer,Values.empty,Function.update]

theorem checked_numeric_targets : ∀ slot : Fin 76,
    (match Reduction.Native.code[slot.val]? with
    | some (.branch target) => decide (target=12 ∨ target=21 ∨ target=30 ∨ target=39 ∨
        target=48 ∨ target=57 ∨ target=66 ∨ target=75)
    | _ => true)=true := by decide +kernel

/-- All actual control transfers enter tables with no presumed numerical facts.
The loop and inactive lanes therefore cannot carry invented register values. -/
theorem entries : NativeFlow.Numeric.Entries (program count left right output scratch) loadContract := by
  intro pc i fetch
  by_cases input : pc<20
  · rw [input_fetch input] at fetch
    obtain ⟨op,found,equal⟩ := Option.map_eq_some_iff.mp fetch
    cases equal
    interval_cases pc <;>
      simp [DotInput.inputProgram,Flow.OperandWindow.program,Flow.OperandWindow.header,
        DotInput.setupCode,DotInput.body,loadCode,PTX.addressCode] at found
    all_goals cases found
    all_goals try trivial
    · intro thread s; exact empty_ready
    · intro thread s; rw [input_entry_table]; exact empty_ready
  · by_cases inside : pc<96
    · have position : pc=20+(pc-20) := by omega
      rw [position,tree_fetch (by omega)] at fetch
      obtain ⟨op,found,equal⟩ := Option.map_eq_some_iff.mp fetch
      have checked := checked_numeric_targets ⟨pc-20,by omega⟩
      rw [found] at checked
      cases op <;> cases equal
      · trivial
      · trivial
      · simp only [decide_eq_true_eq] at checked
        rcases checked with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
        all_goals intro thread s; exact empty_ready
    · have position : pc=96+(pc-96) := by omega
      rw [position,tail_fetch] at fetch
      obtain ⟨op,found,equal⟩ := Option.map_eq_some_iff.mp fetch
      cases equal
      have member := List.mem_of_getElem? found
      simp only [tail,List.mem_cons,List.not_mem_nil,or_false] at member
      rcases member with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> trivial

theorem update_tag (input : Nat → Float) (phase : Fin 8) :
    NativeFlow.Numeric.tag (program count left right output scratch) (loads input phase)
      (storeSite ⟨phase.val+1,by omega⟩) 8=
      some (fun t => values input phase.val t.val+values input phase.val (t.val+stride phase)) := by
  fin_cases phase <;> rfl

/-- The store's numerical value is read from its actual source register. Load
contracts are evidence about the actual whole-history observations. -/
theorem stored {cfg : Config 256} {ctx : Fin 256 → Kernel.Context} {w : Nat}
    (run : NativeFlow.Runs cfg ctx (program count left right output scratch) start events indices final)
    (aligned : Aligned start.core) (entry : ∀ thread, (start.core.lanes thread).pc=0)
    (reads : Reads loadContract events) (phase : Fin 9)
    (known : NativeFlow.Numeric.tag (program count left right output scratch) loadContract (storeSite phase) 8=some answer)
    (observed : events[w]?=some (.data thread access)) (atSite : access.data.pc=storeSite phase) :
    decode access.data.value=answer thread := by
  obtain ⟨before,earlier,earlierIndices,selected,out,suffix,suffixIndices,j,hp,hs,hm,ht,he,hi⟩ := NativeFlow.event_prefix run observed
  obtain ⟨same,i,next,index,fetch,effect⟩ := NativeFlow.step_access_origin hs (List.mem_of_getElem? hm)
  subst selected
  have pc := (NativeFlow.eval_access_pc effect).1.symm.trans atSite
  change (before.core.lanes thread).pc=storeSite phase at pc
  have inv : NativeFlow.Numeric.Invariant (program count left right output scratch) loadContract start := by
    intro t; rw [entry]; exact empty_ready
  have ready := NativeFlow.Numeric.runs_invariant hp aligned inv entries
    (fun t a member => reads t a (by rw [he]; exact List.mem_append_left _ (List.mem_append_left _ member))) thread
  rw [pc] at ready
  have value := ready 8 answer known
  rw [pc,store_fetch] at fetch
  cases fetch
  cases effect with
  | data step => cases step with
    | data step => cases step with
      | store valid => exact value

end PtxTorchLean.Poisson.PTX.Concurrent.Dot.Numeric

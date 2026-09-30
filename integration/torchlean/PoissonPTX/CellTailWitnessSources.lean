import PoissonPTX.CellTailChecks
import PoissonPTX.CellTailResult
import PoissonPTX.ZeroSources

namespace PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.WithOutput.Checks
open Ptx CellMiddle
set_option maxRecDepth 100000
set_option maxHeartbeats 40000000
attribute [local irreducible] result

/-- Check words, alignment and output addresses of this concrete execution.
These finite facts do not replace the general address proof still required. -/
def eventCheck : Event 32 → Bool
  | .data _ a => a.data.value==0 && a.data.address%8==0 &&
      (!(a.space==.global && a.data.store) || decide (160≤a.data.address))
  | .barrier _ => true

theorem event_facts : result.events.all eventCheck=true := by decide +kernel

theorem facts_at (member : Event.data thread a∈result.events) :
    a.data.value=0 ∧ a.data.address%8=0 ∧
      (a.space=.global → a.data.store=true → 160≤a.data.address) := by
  have h := List.all_eq_true.mp event_facts _ member
  simp only [eventCheck,Bool.and_eq_true,beq_iff_eq] at h
  refine ⟨h.1.1,h.1.2,?_⟩
  intro global store
  simpa [global,store] using h.2

theorem compatible : Visibility.Compatible (fun _ _ => 0) result.events (ZeroSources.source result.events) :=
  ZeroSources.compatible (fun _ _ member => (facts_at member).1)

theorem performed : Visibility.Performed result.events (ZeroSources.source result.events) := by
  intro w r writer reader wa ra hw hr write read sw sr ordered j k same
  have aw := (facts_at (List.mem_of_getElem? hw)).2.1
  have ar := (facts_at (List.mem_of_getElem? hr)).2.1
  have hj := j.isLt; have hk := k.isLt
  have addr : wa.data.address=ra.data.address := by omega
  have found : result.events.findIdx (ZeroSources.writes ra.space ra.data.address)<result.events.length := by
    apply List.findIdx_lt_length.mpr
    exact ⟨.data writer wa,List.mem_of_getElem? hw,by simp [ZeroSources.writes,write,sw,sr,addr]⟩
  simp [ZeroSources.source,hr,found]

def launch : Numeric.Launch 2 (fun _ => 0) start.core := {
  generation:=0, reset:=rfl, pcs:=by intro t; rfl,
  global:=by intro t; simp [start,Witness.seed],
  shared:=by intro t; simp [start,Witness.seed],
  lanes:=by intro t; simp [start,Witness.seed],
  rows:=by intro t; simp [start,Witness.seed],
  cols:=by intro t; simp [start,Witness.seed],
  fits:=by decide }

/-- Non-vacuity of the combined numerical theorem, with interleaved global
output stores, all padding returns, and one whole-history source assignment. -/
theorem correspondence (i j : Fin 2) :
    decode ((result.state.core.lanes ⟨i.val*2+j.val,by have := i.isLt; have := j.isLt; omega⟩).regs 11)=
      Spec.get2 (localAction
        (Numeric.initialTensor 2 (fun _ => 0) (fun _ _ => 0) .global 0)
        (Numeric.initialTensor 2 (fun _ => 0) (fun _ _ => 0) .global 64)
        (Numeric.initialTensor 2 (fun _ => 0) (fun _ _ => 0) .global 128)
        (Numeric.initialTensor 2 (fun _ => 0) (fun _ _ => 0) .shared 0)) i j := by
  apply result_under_store_bounds launch (by decide) (by decide) actual_run (by decide)
  · intro w writer wa observed store global
    exact (facts_at (List.mem_of_getElem? observed)).2.2 global store
  · exact compatible
  · exact performed
  · rfl
  · rw [(returned _).2,front_length]; omega

end PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.WithOutput.Checks

import PoissonPTX.CellWholeCompose
import PoissonPTX.CellEntryChecks
import PoissonPTX.CellTailChecks
import PoissonPTX.ZeroSources

namespace PtxTorchLean.Poisson.PTX.CellWhole.Zero
open Ptx
set_option maxRecDepth 100000
set_option maxHeartbeats 40000000

def seed : PTX.State := {
  pc:=0,regs:=fun _ => 0,global:=fun _ => 0,shared:=fun _ => 0,
  globalStart:=0,globalBytes:=512,sharedStart:=0,sharedBytes:=224 }
def start : CellEntry.State 32 := ⟨⟨fun _ => seed,Barrier.reset 0,none⟩,fun _ => false⟩
def cfg : Concurrent.Config 32 := ⟨0,by decide⟩
def bases : Space → Word := fun _ => 0

def prefixCandidate := CellEntry.execute cfg (CellPrologue.threadContext bases 0)
  (CellEntry.program 2 192 224) (fun _ _ => 0) CellEntry.Checks.schedule start
def prefixResult : CellEntry.Outcome 32 := prefixCandidate.getD ⟨start,[],[]⟩
theorem prefix_executed : prefixCandidate=some prefixResult := by
  have yes : prefixCandidate.isSome=true := by decide +kernel
  cases h : prefixCandidate with
  | none => simp [h] at yes
  | some out => simp [prefixResult,h]

def ctx (t : Fin 32) : Kernel.Context := ⟨0,BitVec.ofNat 32 t.val,0⟩
def bodyStart := CellEntry.continuation prefixResult.state
def bodyCandidate := Concurrent.WithTail.execute cfg ctx (Concurrent.CellConsumer.WithOutput.front 2)
  (CellFinal.tail 2 256) (fun _ _ => 0) Concurrent.CellConsumer.WithOutput.Checks.schedule bodyStart
def bodyResult : Concurrent.WithTail.Outcome 32 := bodyCandidate.getD ⟨bodyStart,[]⟩
theorem body_executed : bodyCandidate=some bodyResult := by
  have yes : bodyCandidate.isSome=true := by decide +kernel
  cases h : bodyCandidate with
  | none => simp [h] at yes
  | some out => simp [bodyResult,h]

def events := prefixResult.events++bodyResult.events.map (Relocate.event 21)
def final := Relocate.tailState 21 bodyResult.state

attribute [local irreducible] prefixResult bodyResult events final

theorem actual : Runs cfg bases 0 2 192 224 256 ctx (begin start)
    events prefixResult.indices final := by
  unfold events final
  exact compose (CellEntry.execute_sound prefix_executed) (by decide +kernel) (by decide +kernel)
    (Concurrent.WithTail.execute_sound body_executed)

theorem returned : ∀ t : Fin 32, final.halted t=true ∧
    (final.core.lanes t).pc=21+(Concurrent.CellConsumer.WithOutput.front 2).length+6 := by decide +kernel

theorem four_outputs : (events.filter fun e => match e with
    | .data _ a => a.space==.global && a.data.store
    | _ => false).length=4 := by decide +kernel

theorem zero : Concurrent.ZeroSources.Zero events := by
  have checked : events.all (fun e => match e with
    | .data _ a => a.data.value==0
    | _ => true)=true := by decide +kernel
  intro owner a member
  simpa using List.all_eq_true.mp checked (.data owner a) member

theorem admitted : Concurrent.Visibility.Compatible (fun _ _ => 0) events
    (Concurrent.ZeroSources.source events) := Concurrent.ZeroSources.compatible zero

/-- Actual checked addresses suffice for the necessary performed-write rule. -/
theorem aligned : ∀ owner a, Concurrent.Event.data owner a∈events → a.data.address%8=0 := by
  have checked : events.all (fun e => match e with
    | .data _ a => a.data.address%8==0
    | _ => true)=true := by decide +kernel
  intro owner a member
  simpa using List.all_eq_true.mp checked (.data owner a) member

theorem performed : Concurrent.Visibility.Performed events (Concurrent.ZeroSources.source events) := by
  intro w r writer reader wa ra hw hr write read sw sr ordered j k same
  have aw := aligned writer wa (List.mem_of_getElem? hw)
  have ar := aligned reader ra (List.mem_of_getElem? hr)
  have hj := j.isLt; have hk := k.isLt
  have addr : wa.data.address=ra.data.address := by omega
  have found : events.findIdx (Concurrent.ZeroSources.writes ra.space ra.data.address)<events.length := by
    apply List.findIdx_lt_length.mpr
    exact ⟨.data writer wa,List.mem_of_getElem? hw,by simp [Concurrent.ZeroSources.writes,write,sw,sr,addr]⟩
  simp [Concurrent.ZeroSources.source,hr,found]

theorem indices_admitted : IndexSources.Compatible (fun _ => 0) events prefixResult.indices
    (fun _ _ => .initial) := by
  have checked : prefixResult.indices.all (fun (_,a) => decide (∀ k : Fin 4, IndexSources.byte32 a.value k.val=0))=true := by decide +kernel
  intro r owner a observed k
  have h := List.all_eq_true.mp checked (owner,a) (List.mem_of_getElem? observed)
  exact (of_decide_eq_true h) k

end PtxTorchLean.Poisson.PTX.CellWhole.Zero

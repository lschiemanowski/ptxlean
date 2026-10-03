import PoissonPTX.ReductionComplete

namespace PtxTorchLean.Poisson.PTX.Concurrent.Reduction.Control.Witness256.Checks

def cfg : Config 256 := ⟨0,by decide⟩
def start (input : Nat → Word) : State 256 :=
  ⟨fun t => ⟨0,(fun r => if r=14 then BitVec.ofNat 64 t.val else if r=8 then input t.val else 0),
    (fun _ => 0),(fun _ => 0),0,0,0,2048⟩,Ptx.Barrier.reset 0,none⟩

theorem ready (input : Nat → Word) : ReadyAt 0 0 0 (start input) := by
  refine ⟨?_,by intro t; rfl,rfl,rfl⟩
  intro t
  simp only [Frame,start,↓reduceIte,BitVec.toNat_ofNat]
  simp
  have bound := t.isLt
  omega

/-- A complete admitted execution exists even with arbitrary bit patterns,
including infinities and NaNs; no finite-input restriction was added. -/
theorem arbitrary_words (input : Nat → Word) :
    ∃ final events source,
      Runs cfg program (start input) events final ∧ (∀ t, (final.lanes t).pc=program.length) ∧
      Visibility.Compatible (fun _ _ => 0) events source ∧ Visibility.Repeated.OrderedSources events source ∧
      ∃ (w : Nat) (a : Access), events[w]?=some (.data 0 a) ∧
        a.data.pc=66 ∧ a.data.store=true ∧ a.space=.shared ∧ a.data.address=0 ∧
        decode a.data.value=Binary64.reduce256 (fun i => decode (input i)) := by
  exact exists_correct (cfg:=cfg) (start input) (ready input) (by decide)
    (by intro t; simp [start]) (fun _ _ => 0)

/-- Cancellation still follows the parallel tree's order: this reduction gives
2, whereas the existing sequential fold regression gives 1. -/
theorem cancellation_result :
    ∃ final events source,
      Runs cfg program (start (fun i => encode (Binary64.cancellation i))) events final ∧
      (∀ t, (final.lanes t).pc=program.length) ∧
      Visibility.Compatible (fun _ _ => 0) events source ∧ Visibility.Repeated.OrderedSources events source ∧
      ∃ (w : Nat) (a : Access), events[w]?=some (.data 0 a) ∧
        a.data.pc=66 ∧ a.data.store=true ∧ a.space=.shared ∧ a.data.address=0 ∧
        (decode a.data.value).toBits=0x4000000000000000 := by
  obtain ⟨final,events,source,run,done,compatible,ordered,w,a,found,pc,write,shared,address,value⟩ :=
    arbitrary_words (fun i => encode (Binary64.cancellation i))
  refine ⟨final,events,source,run,done,compatible,ordered,w,a,found,pc,write,shared,address,?_⟩
  simp only [decode_encode] at value
  rw [value]
  exact Binary64.reduction_order_counterexample.2

end PtxTorchLean.Poisson.PTX.Concurrent.Reduction.Control.Witness256.Checks

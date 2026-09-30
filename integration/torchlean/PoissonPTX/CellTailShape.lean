import PoissonPTX.CellTailAddress
import PoissonPTX.ConcurrentAddress

namespace PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.WithOutput.Address
open Ptx

/-- Address registers are not overwritten by the front. A jump beyond its end
can only be the inactive-lane branch to return. All front stores are shared. -/
def fact (width cut : Nat) : Instr → Prop
  | .data op => SharedStore.keeps 0 op ∧ SharedStore.keeps 14 op ∧ SharedStore.keeps 15 op ∧
      (match op with | .store64 sp _ _ => sp=.shared | _ => True)
  | .skip active target => target≤cut ∨ (active=width*width ∧ target=cut+5)
  | .sync _ => True

instance : Decidable (fact width cut i) := by
  cases i <;> simp only [fact] <;> try infer_instance
  cases ‹Op› <;> simp only [SharedStore.keeps] <;> infer_instance

def Checked (width : Nat) : Prop := ∀ i∈front width, fact width (front width).length i
instance : Decidable (Checked width) := by unfold Checked; infer_instance

set_option maxRecDepth 100000 in
set_option maxHeartbeats 30000000 in
theorem checked (lo : 2≤width) (hi : width≤5) : Checked width := by
  interval_cases width <;> decide +kernel

theorem front_keeps (lo : 2≤width) (hi : width≤5)
    (reg : r=0 ∨ r=14 ∨ r=15) : Concurrent.Address.Keeps (front width) r := by
  intro pc op fetch
  have h := checked lo hi _ (List.mem_of_getElem? fetch)
  rcases reg with rfl|rfl|rfl
  · exact h.1
  · exact h.2.1
  · exact h.2.2.1

theorem tail_keeps_register (reg : r=0 ∨ r=14 ∨ r=15) :
    ∀ i∈CellFinal.tail width output, WithTail.keeps r i := by
  rcases reg with rfl|rfl|rfl <;>
    simp [CellFinal.tail,storeCode,addressCode,WithTail.keeps,SharedStore.keeps]

theorem location_eq (base : s.regs 0=t.regs 0) (lane : s.regs 14=t.regs 14)
    (cell : s.regs 15=t.regs 15) :
    CellFinal.location s width output=CellFinal.location t width output := by
  simp [CellFinal.location,CellFinal.indexed,CellFinal.index,address,wide,assign,PTX.advance,base,lane,cell]

def Invariant (width : Nat) (output : Word) (s : WithTail.State n) : Prop :=
  ∀ t, Ready (front width).length width output (t.val<width*width) (s.core.lanes t)

theorem front_ready {n : Nat} {cfg : Config n} {actual : Concurrent.State n}
    {out : Concurrent.Outcome n} {selected : Fin n} (lo : 2≤width) (hi : width≤5)
    (step : Concurrent.Step cfg (front width) selected actual out)
    (aligned : Aligned actual)
    (ready : ∀ t, Ready (front width).length width output (t.val<width*width) (actual.lanes t)) :
    ∀ t, Ready (front width).length width output (t.val<width*width) (out.state.lanes t) := by
  obtain ⟨fresh,i,fetch,dispatch⟩ := step
  have before := (List.getElem?_eq_some_iff.mp fetch).1
  cases dispatch with
  | data hd =>
    intro t
    by_cases eq : t=selected
    · subst t
      apply ready_before
      simpa only [setLane,Function.update_self,data_pc hd] using Nat.succ_le_of_lt before
    · simpa [setLane,Function.update,eq] using ready t
  | @skip active target =>
    intro t
    by_cases eq : t=selected
    · subst t
      simp only [setLane,Function.update_self]
      split
      · exact ready_before (Nat.succ_le_of_lt before)
      · rename_i inactive
        have shape := checked lo hi _ (List.mem_of_getElem? fetch)
        rcases shape with bound|⟨count,ret⟩
        · exact ready_before bound
        · have padding : ¬selected.val<width*width := by simpa [count] using inactive
          simp [Ready,ret,padding]
    · simpa [setLane,Function.update,eq] using ready t
  | @sync resource =>
    intro t
    simp only [synchronize]
    split
    · exact ready t
    · exact ready t
    · rename_i release
      have same := release_aligned cfg actual selected resource aligned release t
      apply ready_before
      change (actual.lanes t).pc+1≤(front width).length
      rw [same]; omega

theorem step_ready (lo : 2≤width) (hi : width≤5)
    (step : WithTail.Step cfg ctx (front width) (CellFinal.tail width output) selected s out)
    (aligned : Aligned s.core) (ready : Invariant width output s) :
    Invariant width output out.state := by
  cases step with
  | front _ h => exact front_ready lo hi h aligned ready
  | tail _ _ past fetch eval =>
    intro t
    by_cases eq : t=selected
    · subst t
      simpa only [WithTail.update,setLane,Function.update_self] using
        tail_ready (ready selected) past fetch eval
    · simpa [WithTail.update,setLane,Function.update,eq] using ready t

theorem runs_ready (lo : 2≤width) (hi : width≤5)
    (run : WithTail.Runs cfg ctx (front width) (CellFinal.tail width output) start events final)
    (aligned : Aligned start.core) (ready : Invariant width output start) :
    Invariant width output final := by
  induction run with
  | nil => exact ready
  | cons step _ ih => exact ih (WithTail.step_aligned step aligned) (step_ready lo hi step aligned ready)

end PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.WithOutput.Address

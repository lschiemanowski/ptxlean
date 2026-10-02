import PoissonPTX.CellTailStores
import PoissonPTX.ConcurrentPadding

namespace PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.WithOutput.Padding

/-- Padding lanes may visit guards/barriers or the final return, but cannot
enter any output-address or store instruction. -/
def allowed (width pc : Nat) : Bool :=
  if pc<(front width).length then Concurrent.Padding.outside (front width) pc
  else decide ((front width).length+5≤pc)

def Boundaries (width : Nat) : Prop :=
  ∀ pc∈List.range (front width).length,
    match (front width)[pc]? with
    | some (.skip count target) => count=width*width ∧ allowed width target=true
    | some (.sync _) => allowed width (pc+1)=true
    | _ => True

instance : Decidable (Boundaries width) := by
  unfold Boundaries
  have : ∀ pc : Nat, Decidable (match (front width)[pc]? with
      | some (.skip count target) => count=width*width ∧ allowed width target=true
      | some (.sync _) => allowed width (pc+1)=true
      | _ => True) := by
    intro pc
    cases (front width)[pc]? with
    | none => infer_instance
    | some op => cases op <;> infer_instance
  infer_instance

/-- Traverse fetched instructions once; only guards and barriers need a target
check. The soundness lemma below recovers the original per-PC condition. -/
def checkBoundaries (width : Nat) : Bool :=
  (front width).zipIdx.all fun (op,pc) => match op with
    | .skip count target => decide (count=width*width) && allowed width target
    | .sync _ => allowed width (pc+1)
    | .data _ => true

theorem checkBoundaries_sound (checked : checkBoundaries width=true) : Boundaries width := by
  intro pc inside
  cases fetch : (front width)[pc]? with
  | none => trivial
  | some op =>
    have found := List.all_eq_true.mp checked (op,pc) (List.mk_mem_zipIdx_iff_getElem?.mpr fetch)
    cases op <;> simpa using found

set_option maxRecDepth 100000 in
set_option maxHeartbeats 30000000 in
theorem boundaries (lo : 2≤width) (hi : width≤5) : Boundaries width := by
  apply checkBoundaries_sound
  interval_cases width <;> decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 30000000 in
theorem initial (lo : 2≤width) (hi : width≤5) : allowed width 0=true := by
  interval_cases width <;> decide +kernel

def Invariant (width : Nat) (s : WithTail.State n) : Prop :=
  ∀ thread, width*width≤thread.val → allowed width (s.core.lanes thread).pc=true

theorem step_invariant (lo : 2≤width) (hi : width≤5)
    (step : WithTail.Step cfg ctx (front width) (CellFinal.tail width output) selected s out)
    (aligned : Aligned s.core) (inv : Invariant width s) : Invariant width out.state := by
  cases step with
  | front _ one =>
    obtain ⟨fresh,op,fetch,dispatch⟩ := one
    have before := (List.getElem?_eq_some_iff.mp fetch).1
    have shape := boundaries lo hi _ (List.mem_range.mpr before)
    rw [fetch] at shape
    cases dispatch with
    | data hd =>
      intro thread inactive
      by_cases eq : thread=selected
      · subst thread
        have bad := inv selected inactive
        simp only [allowed,if_pos before,Concurrent.Padding.outside,fetch,Bool.false_eq_true] at bad
      · simpa [setLane,Function.update,eq] using inv thread inactive
    | skip =>
      intro thread inactive
      by_cases eq : thread=selected
      · subst thread
        simp only [setLane,Function.update_self]
        split
        · omega
        · exact shape.2
      · simpa [setLane,Function.update,eq] using inv thread inactive
    | @sync resource =>
      intro thread inactive
      simp only [synchronize]
      split
      · exact inv thread inactive
      · exact inv thread inactive
      · rename_i released
        have same := release_aligned cfg s.core selected resource aligned released thread
        simpa [advance,same] using shape
  | tail _ _ past fetch eval =>
    intro thread inactive
    by_cases eq : thread=selected
    · subst thread
      have before := inv selected inactive
      have bound : (front width).length+5≤(s.core.lanes selected).pc := by simpa [allowed,show ¬(s.core.lanes selected).pc<(front width).length by omega] using before
      have pc := Kernel.eval_pc eval
      simp only [WithTail.lane] at pc
      simp only [WithTail.update,setLane,Function.update_self]
      unfold allowed
      rw [if_neg (by omega),decide_eq_true_eq]
      omega
    · simpa [WithTail.update,setLane,Function.update,eq] using inv thread inactive

theorem runs_invariant (lo : 2≤width) (hi : width≤5)
    (run : WithTail.Runs cfg ctx (front width) (CellFinal.tail width output) start events final)
    (aligned : Aligned start.core) (inv : Invariant width start) : Invariant width final := by
  induction run with
  | nil => exact inv
  | cons step rest ih => exact ih (WithTail.step_aligned step aligned) (step_invariant lo hi step aligned inv)

/-- Every actual data record is owned by an active matrix lane. In particular,
padding cannot write into the following cell's contiguous output region. -/
theorem access_active (lo : 2≤width) (hi : width≤5)
    (run : WithTail.Runs cfg ctx (front width) (CellFinal.tail width output) start events final)
    (aligned : Aligned start.core) (pcs : ∀ t, (start.core.lanes t).pc=0)
    (member : Event.data owner access∈events) : owner.val<width*width := by
  obtain ⟨before,earlier,selected,out,rest,prior,step,record,suffix⟩ := Address.access_prefix run member
  have inv : Invariant width before := runs_invariant lo hi prior aligned (by intro t _; rw [pcs]; exact initial lo hi)
  by_contra inactive
  have inactive : width*width≤owner.val := by omega
  cases step with
  | front _ one =>
    obtain ⟨eq,op,next,fetch,execution⟩ := step_access_origin one record
    subst selected
    have bad := inv owner inactive
    have before := (List.getElem?_eq_some_iff.mp fetch).1
    simp only [allowed,if_pos before,Concurrent.Padding.outside,fetch,Bool.false_eq_true] at bad
  | tail _ _ past fetch eval =>
    simp only [List.mem_map,Option.mem_toList] at record
    obtain ⟨a,observed,eq⟩ := record
    cases eq
    have permitted := inv owner inactive
    have low : (front width).length+5≤(before.core.lanes owner).pc := by
      simpa [allowed,show ¬(before.core.lanes owner).pc<(front width).length by omega] using permitted
    have bound := (List.getElem?_eq_some_iff.mp fetch).1
    rw [tail_length] at bound
    have atReturn : (before.core.lanes owner).pc-(front width).length=5 := by omega
    rw [atReturn] at fetch
    simp [CellFinal.tail,storeCode,addressCode] at fetch
    subst_vars
    simp [WithTail.access] at observed

end PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.WithOutput.Padding

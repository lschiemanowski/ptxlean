import PoissonPTX.TailRunProjection
import PoissonPTX.CellOutputSeparation

namespace PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.WithOutput
open WithTail

/-- Only the final inactive-lane branch is extended to the real return.
Earlier skips still lead to their actual barriers. -/
def redirect (cut returnPC : Nat) : Instr → Instr
  | .skip active target => .skip active (if target=cut then returnPC else target)
  | i => i

def front (width : Nat) : List Instr :=
  (program width).map (redirect (program width).length ((program width).length+5))

theorem tail_length : (CellFinal.tail width output).length=6 := rfl

theorem front_length : (front width).length=(program width).length := List.length_map _

/-- Every branch target is within the arithmetic program before redirection. -/
def Bounded (code : List Instr) : Prop :=
  ∀ i∈code, match i with | .skip _ target => target≤code.length | _ => True

instance : Decidable (Bounded code) := by
  unfold Bounded
  have : ∀ i : Instr, Decidable (match i with | .skip _ target => target≤code.length | _ => True) := by
    intro i; cases i <;> infer_instance
  infer_instance

set_option maxRecDepth 100000 in
set_option maxHeartbeats 30000000 in
theorem bounded (width : Nat) (lo : 2≤width) (hi : width≤5) : Bounded (program width) := by
  interval_cases width <;> decide +kernel

/-- Clipping the actual return branch recovers the existing arithmetic program,
instruction for instruction, for each supported element order. -/
theorem clipped (lo : 2≤width) (hi : width≤5) :
    (front width).map (clip (front width).length)=program width := by
  rw [front_length,front,List.map_map]
  conv_rhs => rw [← List.map_id (program width)]
  apply List.map_congr_left
  intro i member
  have bound := bounded width lo hi i member
  cases i with
  | data => rfl
  | sync => rfl
  | skip active target =>
    dsimp [Function.comp,redirect,clip]
    split
    · simp [‹target=(program width).length›]
    · exact congrArg (Instr.skip active) (Nat.min_eq_left bound)

theorem tail_keeps : ∀ i∈CellFinal.tail width output, keeps 11 i := by
  simp [CellFinal.tail,storeCode,addressCode,keeps,SharedStore.keeps]

/-- Inactive final consumers jump over all stores to the fetched return. -/
theorem padding_return :
    (front width)[(CellMiddle.Checks.program width).length]?=
      some (.skip (width*width) ((front width).length+5)) := by
  rw [front_length,front,List.getElem?_map]
  have atGuard : (program width)[(CellMiddle.Checks.program width).length]?=
      some (.skip (width*width) (program width).length) := by
    simp only [program,List.getElem?_append_right (Nat.le_refl _),Nat.sub_self,suffix,
      List.singleton_append,List.getElem?_cons_zero,List.length_append,List.length_cons,List.length_map]
    congr 2; omega
  rw [atGuard]
  simp [redirect]

/-- Extract a genuine arithmetic run and its occurrence embedding from the
actual interleaved front/index/store/return execution. -/
theorem arithmetic (lo : 2≤width) (hi : width≤5)
    (run : WithTail.Runs cfg ctx (front width) (CellFinal.tail width output) start events final)
    (aligned : Aligned start.core) (pcs : ∀ t, (start.core.lanes t).pc=0) :
    ∃ small shadow,
      Concurrent.Runs cfg (program width) start.core small shadow ∧
      Nonempty (Projection.Embedding small events) ∧
      Related (program width).length 11 final.core shadow := by
  obtain ⟨small,shadow,run',embedding,related⟩ :=
    project run aligned tail_keeps (related_refl (tracked:=11) (by intro t; rw [pcs]; omega))
  rw [clipped lo hi] at run'
  rw [front_length] at related
  exact ⟨small,shadow,run',embedding,related⟩


/-- All omitted accesses of this concrete tail are global stores. This fact is
derived from its instruction list, not assumed about a projected history. -/
def OutputEvent : Event n → Prop
  | .data _ a => a.space=.global ∧ a.data.store=true
  | .barrier _ => False

theorem tail_events (member : i∈CellFinal.tail width output)
    (observed : WithTail.access i s t=some a) : OutputEvent (Event.data thread a) := by
  simp only [CellFinal.tail,storeCode,addressCode,List.map_cons,List.map_nil,
    List.cons_append,List.nil_append,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals simp only [WithTail.access] at observed
  all_goals cases observed
  exact ⟨rfl,rfl⟩

theorem arithmetic_filtered (lo : 2≤width) (hi : width≤5)
    (run : WithTail.Runs cfg ctx (front width) (CellFinal.tail width output) start events final)
    (aligned : Aligned start.core) (pcs : ∀ t, (start.core.lanes t).pc=0) :
    ∃ small shadow,
      Concurrent.Runs cfg (program width) start.core small shadow ∧
      ∃ embedding : Projection.Embedding small events,
        Projection.Omitted OutputEvent embedding ∧
        Related (program width).length 11 final.core shadow := by
  obtain ⟨small,shadow,run',embedding,omitted,related⟩ :=
    project_filtered run (fun _ member _ _ _ _ observed => tail_events member observed)
      aligned tail_keeps (related_refl (tracked:=11) (by intro t; rw [pcs]; omega))
  rw [clipped lo hi] at run'
  rw [front_length] at related
  exact ⟨small,shadow,run',embedding,omitted,related⟩

end PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.WithOutput

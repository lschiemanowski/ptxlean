import PoissonPTX.ObservedReplay
import PoissonPTX.ControlFlowSequence
import PoissonPTX.NativeFlowAccessOrder

namespace PtxTorchLean.Poisson.PTX.Flow.Observed

/-- Straight-line instructions, including a predicated return, advance the
actual instruction counter. This lemma does not replay candidate loads. -/
theorem eval_linear_pc (actual : Eval ctx i s t access index) (linear : Flow.linear i=true) :
    t.core.pc=s.core.pc+1 := by
  cases actual with
  | data step => exact Indexed.Candidate.data_pc step
  | simple ordinary => exact Flow.linear_pc (.simple ordinary) linear

theorem word_lower (run : Runs ctx program s words indices t)
    (linear : ∀ i∈program, Flow.linear i=true) (member : a∈words) : s.core.pc≤a.data.pc := by
  induction run with
  | nil => simp at member
  | @cons s middle access index words indices t step rest ih =>
    obtain ⟨running,i,fetch,effect⟩ := step
    rcases List.mem_append.mp member with head | tail
    · cases access with
      | none => simp at head
      | some observed =>
        have same : a=observed := by simpa using head
        subst a
        exact Nat.le_of_eq (Concurrent.NativeFlow.eval_access_pc effect).1.symm
    · have later := ih tail
      have pc := eval_linear_pc effect (linear i (List.mem_of_getElem? fetch))
      omega

/-- Only later reads need preservation after a store. Unlike full physical
separation, this permits an in-place write after the last read of that word. -/
theorem step_future_frame (step : Step ctx program s t access index)
    (frame : ReadFrame initial words indices s.core)
    (wordApart : ∀ a, access=some a → a.data.store=true → ∀ r∈words, r.data.store=false → a.space=r.space →
      a.data.address+8≤r.data.address ∨ r.data.address+8≤a.data.address)
    (indexApart : ∀ a, access=some a → a.data.store=true → a.space=.global → ∀ r∈indices,
      a.data.address+8≤r.address ∨ r.address+4≤a.data.address) : ReadFrame initial words indices t.core := by
  obtain ⟨_,_,_,effect⟩ := step
  cases effect with
  | simple => exact simple_frame frame
  | data one =>
    cases one with
    | data one =>
      cases one with
      | ordinary plain execution =>
        cases execution <;> simp_all [Concurrent.ordinary]
        all_goals exact frame
      | load => exact frame
      | store valid => exact put_frame frame (wordApart _ rfl rfl) (indexApart _ rfl rfl)
    | _ => exact frame

/-- Reconstruct a scalar execution from admitted initial read values when only
writes preceding a read must be disjoint. No value of an in-place output is
assumed, and past reads need not remain unchanged after their final use. -/
theorem replay_temporal (run : Runs ctx program s words indices t)
    (linear : ∀ i∈program, Flow.linear i=true)
    (wordValues : ∀ a∈words, a.data.store=false → a.data.value=read64 (initial a.space) a.data.address)
    (indexValues : ∀ a∈indices, a.value=read32 (initial .global) a.address)
    (wordApart : ∀ w∈words, w.data.store=true → ∀ r∈words, r.data.store=false → w.space=r.space → w.data.pc<r.data.pc →
      w.data.address+8≤r.data.address ∨ r.data.address+8≤w.data.address)
    (indexApart : ∀ w∈words, w.data.store=true → w.space=.global → ∀ r∈indices,
      w.data.address+8≤r.address ∨ r.address+4≤w.data.address)
    (frame : ReadFrame initial words indices s.core) : Flow.Runs ctx program s t := by
  induction run with
  | nil => exact .nil
  | @cons s middle access index words indices t step rest ih =>
    have recorded : ∀ a, access=some a → a∈access.toList++words := by intro a eq; simp [eq]
    have recordedIndex : ∀ a, index=some a → a∈index.toList++indices := by intro a eq; simp [eq]
    have one := replay_step step
      (fun a eq read => (wordValues a (recorded a eq) read).trans (frame.1 a (recorded a eq) read).symm)
      (fun a eq => (indexValues a (recordedIndex a eq)).trans (frame.2 a (recordedIndex a eq)).symm)
    have nextFrame : ReadFrame initial words indices middle.core := by
      apply step_future_frame step
      · exact ⟨fun a mem => frame.1 a (List.mem_append_right _ mem),fun a mem => frame.2 a (List.mem_append_right _ mem)⟩
      · intro a seen store r member read same
        apply wordApart a (recorded a seen) store r (List.mem_append_right _ member) read same
        obtain ⟨_,i,fetch,effect⟩ := step
        have post := (Concurrent.NativeFlow.eval_access_pc (seen ▸ effect)).2
        have lower := word_lower rest linear member
        omega
      · intro a seen store global r member
        exact indexApart a (recorded a seen) store global r (List.mem_append_right _ member)
    exact .cons one (ih (fun a mem => wordValues a (List.mem_append_right _ mem))
      (fun a mem => indexValues a (List.mem_append_right _ mem))
      (fun w mem store r observed => wordApart w (List.mem_append_right _ mem) store r (List.mem_append_right _ observed))
      (fun w mem store global r observed => indexApart w (List.mem_append_right _ mem) store global r (List.mem_append_right _ observed)) nextFrame)

end PtxTorchLean.Poisson.PTX.Flow.Observed

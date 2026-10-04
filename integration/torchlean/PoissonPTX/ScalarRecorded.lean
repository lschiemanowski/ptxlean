import PoissonPTX.ScalarSourceBridge

namespace PtxTorchLean.Poisson.PTX.Scalar.Observed

/-- Each recorded read agrees with the actual preceding stores. Used to
construct admitted witnesses from ordinary executions, never as a universal
candidate-execution premise. -/
def CurrentReads (memory : Space → Memory) : List Sources.Access → Prop
  | [] => True
  | a::rest => ReadValues memory [a] ∧ CurrentReads (Sources.applyAccess memory a) rest

theorem current_append (one : CurrentReads memory first) (two : CurrentReads (Sources.publish memory first) rest) :
    CurrentReads memory (first++rest) := by
  induction first generalizing memory with
  | nil => exact two
  | cons a first ih => exact ⟨one.1,ih one.2 two⟩

theorem eval_current (actual : Eval ctx i s t events) (reads : ReadValues s.core.memory events) : CurrentReads s.core.memory events := by
  rcases eval_events actual with empty | ⟨a,single,pc⟩
  · simp [empty,CurrentReads]
  · rw [single] at reads ⊢
    exact ⟨reads,trivial⟩

theorem sequence_recorded (actual : Scalar.Sequence ctx code s t) :
    ∃ events, Sequence ctx code s events t ∧ CurrentReads s.core.memory events := by
  induction actual with
  | nil => exact ⟨[],.nil,trivial⟩
  | cons alive step rest ih =>
    obtain ⟨first,recorded,reads⟩ := eval_witness step
    obtain ⟨tail,run,current⟩ := ih
    refine ⟨first++tail,.cons alive recorded run,current_append (eval_current recorded reads) ?_⟩
    rw [← eval_memory recorded]
    exact current

/-- Earlier stores cannot affect any later read byte when the actual access
footprints establish disjointness. This turns recorded current reads into
initial-byte source witnesses. -/
theorem current_initial (current : CurrentReads memory events) (order : events.Pairwise (fun a b => a.pc<b.pc))
    (apart : FutureSeparate events) : ReadValues memory events := by
  induction events generalizing memory with
  | nil => simp [ReadValues]
  | cons a events ih =>
    obtain ⟨before,tailOrder⟩ := List.pairwise_cons.mp order
    have tail := ih current.2 tailOrder (fun w wm write r rm => apart w (by simp [wm]) write r (by simp [rm]))
    intro r member read k small
    rcases List.mem_cons.mp member with rfl | member
    · exact current.1 r (by simp) read k small
    · exact (tail r member read k small).trans (Sources.apply_outside (by
        intro write space
        have separated := apart a (by simp) write r (by simp [member]) read space (before r member)
        omega))

theorem initial_compatible (reads : ReadValues memory events) : Sources.Compatible memory events (fun _ _ => .initial) := by
  intro r ra found read k small
  exact reads ra (List.mem_of_getElem? found) read k small

end PtxTorchLean.Poisson.PTX.Scalar.Observed

namespace PtxTorchLean.Poisson.PTX.Scalar
variable {a : Arena} {chunks : List Chunk}

/-- Construct both a candidate instruction history and its initial-byte
admission from an ordinary execution. Numerical values remain unrestricted. -/
theorem chunks_recorded (actual : Scalar.Sequence ctx (chunksCode a.offset chunks) s t)
    (valid : ∀ chunk∈chunks, chunk.valid) (running : s.halted=false) (ready : a.Ready s)
    (ordered : ReadBeforeWrite (footprints a.offset s.core.pc chunks)) :
    ∃ events, Observed.Sequence ctx (chunksCode a.offset chunks) s events t ∧
      Sources.Compatible s.core.memory events (fun _ _ => .initial) ∧ Sources.NoFuture events (fun _ _ => .initial) := by
  obtain ⟨events,recorded,current⟩ := Observed.sequence_recorded actual
  have mapped := chunks_accesses recorded valid running ready
  have order := Observed.sequence_order recorded (fun i mem => (chunks_safe valid i mem).2)
  have apart := mapped_future_separate mapped ordered
  exact ⟨events,recorded,Observed.initial_compatible (Observed.current_initial current order apart),Sources.initial_no_future⟩

end PtxTorchLean.Poisson.PTX.Scalar

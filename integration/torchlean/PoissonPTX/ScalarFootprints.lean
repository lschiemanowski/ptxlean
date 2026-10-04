import PoissonPTX.ScalarChunks

namespace PtxTorchLean.Poisson.PTX.Scalar
variable {chunks : List Chunk} {events : List Sources.Access} {plan : List Footprint}
  {rf wf : Footprint} {ra wa : Sources.Access}

theorem chunks_safe (valid : ∀ chunk∈chunks, chunk.valid) :
    ∀ i∈chunksCode offset chunks, Observed.keepsBase i=true ∧ segment i=true := by
  intro i member
  obtain ⟨chunk,member,inCode⟩ := List.mem_flatMap.mp member
  exact Chunk.safe (valid chunk member) i inCode

theorem chunks_accesses {a : Arena} (actual : Observed.Sequence ctx (chunksCode a.offset chunks) s events t)
    (valid : ∀ chunk∈chunks, chunk.valid) (running : s.halted=false) (ready : a.Ready s) :
    ∀ event∈events, ∃ f∈footprints a.offset s.core.pc chunks, f.Matches a event := by
  induction chunks generalizing s events with
  | nil => cases actual; simp
  | cons chunk chunks ih =>
    change Observed.Sequence ctx (chunk.code a.offset++chunksCode a.offset chunks) s events t at actual
    obtain ⟨middle,first,rest,one,two,same⟩ := Observed.sequence_split _ _ actual
    have safe := Chunk.safe (offset:=a.offset) (valid chunk (by simp))
    have nextReady := Observed.sequence_ready one (fun i mem => (safe i mem).1) ready
    have nextRunning := (Observed.sequence_running one (fun i mem => (safe i mem).2)).trans running
    have nextPC := Observed.sequence_position one (fun i mem => (safe i mem).2)
    have head := Chunk.accesses one (valid chunk (by simp)) running ready
    have tail := ih two (fun c mem => valid c (by simp [mem])) nextRunning nextReady
    intro event member
    rw [same] at member
    rcases List.mem_append.mp member with before | after
    · obtain ⟨f,member,witness⟩ := head event before
      exact ⟨f,List.mem_append_left _ member,witness⟩
    · obtain ⟨f,member,witness⟩ := tail event after
      rw [nextPC] at member
      exact ⟨f,List.mem_append_right _ member,witness⟩

/-- Every read of a field precedes every write to that field. This is checked
on value-free instruction footprints, not on assumed load results. -/
def ReadBeforeWrite (footprints : List Footprint) : Prop :=
  ∀ r∈footprints, r.store=false → ∀ w∈footprints, w.store=true → r.field=w.field → r.pc<w.pc

theorem mapped_future_separate {a : Arena}
    (mapped : ∀ event∈events, ∃ f∈plan, f.Matches a event)
    (ordered : ReadBeforeWrite plan) : Observed.FutureSeparate events := by
  intro w writeMem write r readMem read space before
  obtain ⟨wf,wm,wp,ws,wspace,wa,ww⟩ := mapped w writeMem
  obtain ⟨rf,rm,rp,rs,rspace,ra,rw⟩ := mapped r readMem
  have different : wf.field≠rf.field := by
    intro same
    have order := ordered rf rm (rs.symm.trans read) wf wm (ws.symm.trans write) same.symm
    omega
  have apart := a.separate wf.field rf.field different
  simpa only [wa,ra,ww,rw] using apart

/-- An overlapping read/store byte must belong to the same named field.
Distinct fields cannot alias, including four/eight-byte pairs. -/
theorem same_field_of_byte {a : Arena} (read : rf.Matches a ra) (write : wf.Matches a wa)
    (j k : Fin 8) (smallj : j.val<wa.width.bytes) (smallk : k.val<ra.width.bytes)
    (same : wa.address+j.val=ra.address+k.val) : wf.field=rf.field := by
  by_contra different
  have apart := a.separate wf.field rf.field different
  rw [read.2.2.2.1,write.2.2.2.1] at same
  rw [read.2.2.2.2] at smallk
  rw [write.2.2.2.2] at smallj
  omega

end PtxTorchLean.Poisson.PTX.Scalar

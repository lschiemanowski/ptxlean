import PoissonPTX.ScalarFootprints

namespace PtxTorchLean.Poisson.PTX.Scalar
variable {r w : Nat} {ra wa : Sources.Access} {chunks : List Chunk} {a : Arena} {events : List Sources.Access} {plan : List Footprint}

theorem index_before_of_pc (ordered : events.Pairwise (fun a b => a.pc<b.pc))
    (hr : events[r]?=some ra) (hw : events[w]?=some wa) (before : ra.pc<wa.pc) : r<w := by
  have rr := List.getElem?_eq_some_iff.mp hr
  have ww := List.getElem?_eq_some_iff.mp hw
  by_contra notBefore
  have le : w≤r := by omega
  rcases lt_or_eq_of_le le with less | same
  · have backwards := List.pairwise_iff_getElem.mp ordered w r ww.1 rr.1 less
    rw [ww.2,rr.2] at backwards
    omega
  · subst w
    have equal : ra=wa := Option.some.inj (hr.symm.trans hw)
    subst ra
    omega

theorem mapped_writers (mapped : ∀ event∈events, ∃ f∈plan, f.Matches a event)
    (ordered : ReadBeforeWrite plan) (positions : events.Pairwise (fun a b => a.pc<b.pc))
    (found : events[r]?=some ra) (read : ra.store=false)
    (stored : events[w]?=some wa) (write : wa.store=true)
    (j k : Fin 8) (smallj : j.val<wa.width.bytes) (smallk : k.val<ra.width.bytes)
    (same : wa.address+j.val=ra.address+k.val) : r<w ∧ wa.address=ra.address ∧ wa.width=ra.width := by
  obtain ⟨rf,rm,rmatch⟩ := mapped ra (List.mem_of_getElem? found)
  obtain ⟨wf,wm,wmatch⟩ := mapped wa (List.mem_of_getElem? stored)
  have field := same_field_of_byte rmatch wmatch j k smallj smallk same
  have before := ordered rf rm (rmatch.2.1.symm.trans read) wf wm (wmatch.2.1.symm.trans write) field.symm
  have actualBefore : ra.pc<wa.pc := by rw [rmatch.1,wmatch.1]; exact before
  refine ⟨index_before_of_pc positions found stored actualBefore,?_,?_⟩
  · rw [wmatch.2.2.2.1,rmatch.2.2.2.1,field]
  · have widths : wa.width.bytes=ra.width.bytes := by rw [wmatch.2.2.2.2,rmatch.2.2.2.2,field]
    cases left:wa.width <;> cases right:ra.width <;> simp_all [Sources.Width.bytes]

/-- A value-free footprint check discharges the writer/separation obligations
of source replay for every actual execution of the compiled chunk list. -/
theorem chunks_replay (actual : Observed.Sequence ctx (chunksCode a.offset chunks) s events t)
    (valid : ∀ chunk∈chunks, chunk.valid) (running : s.halted=false) (ready : a.Ready s)
    (ordered : ReadBeforeWrite (footprints a.offset s.core.pc chunks))
    (compatible : Sources.Compatible s.core.memory events source) (admitted : Sources.NoFuture events source) :
    Scalar.Sequence ctx (chunksCode a.offset chunks) s t := by
  have plain : ∀ i∈chunksCode a.offset chunks, segment i=true := fun i mem => (chunks_safe valid i mem).2
  have mapped := chunks_accesses actual valid running ready
  have positions := Observed.sequence_order actual plain
  apply Observed.admitted_sequence actual plain compatible admitted
  · intro r ra found read w wa stored write space j k smallj smallk same
    exact mapped_writers mapped ordered positions found read stored write j k smallj smallk same
  · exact mapped_future_separate mapped ordered

end PtxTorchLean.Poisson.PTX.Scalar

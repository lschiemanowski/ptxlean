import PoissonPTX.ScalarObservedAccess

namespace PtxTorchLean.Poisson.PTX.Scalar.Observed
variable {a : Arena} {s : Flow.State} {field : Field}

def TransferAt (a : Arena) (pc : Nat) (field : Field) (store : Bool) (events : List Sources.Access) : Prop :=
  ∃ event, events=[event] ∧ event.pc=pc+3 ∧ event.store=store ∧ event.space=.global ∧
    event.address=a.slot field ∧ event.width.bytes=field.width

theorem load64_transfer (actual : Sequence ctx (load64Code dst (a.offset field)) s events t)
    (running : s.halted=false) (ready : a.Ready s) (width : field.width=8) : TransferAt a s.core.pc field false events := by
  change Sequence ctx (address8Code (a.offset field)++[.base (.data (.data (.load64 .global dst (.reg 2))))]) s events t at actual
  obtain ⟨middle,first,rest,pre,post,whole⟩ := sequence_split _ _ actual
  obtain ⟨empty,same⟩ := address8_state pre running
  rw [same] at post
  obtain ⟨value,loaded⟩ := load64_access post
  rw [empty,loaded,List.nil_append] at whole
  refine ⟨_,whole,?_,rfl,rfl,?_,width.symm⟩
  · exact (addressed_address (field:=field) ready).1
  · exact (addressed_address (field:=field) ready).2

theorem store64_transfer (actual : Sequence ctx (store64Code (a.offset field) value) s events t)
    (running : s.halted=false) (ready : a.Ready s) (width : field.width=8) : TransferAt a s.core.pc field true events := by
  change Sequence ctx (address8Code (a.offset field)++[.base (.data (.data (.store64 .global (.reg 2) value)))]) s events t at actual
  obtain ⟨middle,first,rest,pre,post,whole⟩ := sequence_split _ _ actual
  obtain ⟨empty,same⟩ := address8_state pre running
  rw [same] at post
  have stored := store64_access post
  rw [empty,stored,List.nil_append] at whole
  refine ⟨_,whole,?_,rfl,rfl,?_,width.symm⟩
  · exact (addressed_address (field:=field) ready).1
  · exact (addressed_address (field:=field) ready).2

theorem load32_transfer (actual : Sequence ctx (load32Code dst (a.offset field)) s events t)
    (running : s.halted=false) (ready : a.Ready s) (width : field.width=4) : TransferAt a s.core.pc field false events := by
  obtain ⟨middle,first,rest,pre,post,whole⟩ := sequence_split _ _ actual
  obtain ⟨empty,same⟩ := address4_state pre running
  rw [same] at post
  obtain ⟨value,loaded⟩ := load32_access post
  rw [empty,loaded,List.nil_append] at whole
  refine ⟨_,whole,?_,rfl,rfl,?_,width.symm⟩
  · exact (addressed_address (field:=field) ready).1
  · exact (addressed_address (field:=field) ready).2

theorem store32_transfer (actual : Sequence ctx (store32Code (a.offset field) value) s events t)
    (running : s.halted=false) (ready : a.Ready s) (width : field.width=4) : TransferAt a s.core.pc field true events := by
  obtain ⟨middle,first,rest,pre,post,whole⟩ := sequence_split _ _ actual
  obtain ⟨empty,same⟩ := address4_state pre running
  rw [same] at post
  have stored := store32_access post
  rw [empty,stored,List.nil_append] at whole
  refine ⟨_,whole,?_,rfl,rfl,?_,width.symm⟩
  · exact (addressed_address (field:=field) ready).1
  · exact (addressed_address (field:=field) ready).2

end PtxTorchLean.Poisson.PTX.Scalar.Observed

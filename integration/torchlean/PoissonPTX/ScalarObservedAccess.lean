import PoissonPTX.ScalarObservedAddress

namespace PtxTorchLean.Poisson.PTX.Scalar.Observed

theorem load64_access (actual : Sequence ctx [.base (.data (.data (.load64 sp dst addr)))] s events t) :
    ∃ value, events=[Sources.word ⟨sp,⟨s.core.pc,false,(addr.eval s.core).toNat,value⟩⟩] := by
  cases actual with
  | cons alive step rest =>
    cases rest
    cases step with
    | extra plain => simp [extra] at plain
    | base step =>
      cases step with
      | simple ordinary => exact False.elim (ordinary _ rfl)
      | data step =>
        cases step with
        | data step =>
          cases step with
          | ordinary plain _ => simp [Concurrent.ordinary] at plain
          | load => exact ⟨_,rfl⟩

theorem store64_access (actual : Sequence ctx [.base (.data (.data (.store64 sp addr value)))] s events t) :
    events=[Sources.word ⟨sp,⟨s.core.pc,true,(addr.eval s.core).toNat,value.eval s.core⟩⟩] := by
  cases actual with
  | cons alive step rest =>
    cases rest
    cases step with
    | extra plain => simp [extra] at plain
    | base step =>
      cases step with
      | simple ordinary => exact False.elim (ordinary _ rfl)
      | data step =>
        cases step with
        | data step =>
          cases step with
          | ordinary plain _ => simp [Concurrent.ordinary] at plain
          | store => rfl

theorem load32_access (actual : Sequence ctx [.base (.data (.load32 dst addr))] s events t) :
    ∃ value, events=[Sources.flag s.core.pc false (s.core.regs addr).toNat value] := by
  cases actual with
  | cons alive step rest =>
    cases rest
    cases step with
    | extra plain => simp [extra] at plain
    | base step =>
      cases step with
      | simple ordinary => exact False.elim (ordinary _ rfl)
      | data step => cases step; exact ⟨_,rfl⟩

theorem store32_access (actual : Sequence ctx [.store32 addr value] s events t) :
    events=[Sources.flag s.core.pc true (addr.eval s.core).toNat (Kernel.u32 (value.eval s.core))] := by
  cases actual with
  | cons alive step rest =>
    cases rest
    cases step with
    | extra plain => simp [extra] at plain
    | store32 => rfl

end PtxTorchLean.Poisson.PTX.Scalar.Observed

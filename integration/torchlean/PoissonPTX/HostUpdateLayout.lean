import PoissonPTX.HostLayout

namespace PtxTorchLean.Poisson.PTX.Host

def updateField : UpdateXRZ.Field → Field
  | .p => .p | .x => .x | .ap => .ap | .r => .r | .diagonal => .diagonal | .z => .z

theorem update_fields (f : UpdateXRZ.Field) :
    (updateField f).count n e w=n ∧ (updateField f).width=8 := by
  cases f <;> simp [updateField,Field.count,Field.width]

def Layout.updateXRZ (a : Layout n e w) : UpdateXRZ.Arena n where
  base:=a.base
  alpha:=a.offset (.scalar .alpha)
  boundary:=a.offset .boundary
  vector:=fun f => a.offset (updateField f)
  bytes:=a.bytes
  small:=a.small
  aligned:=a.baseAligned
  noWrap:=a.noWrap
  alphaAligned:=a.aligned _
  boundaryAligned:=a.align_width .boundary
  vectorAligned:=fun f => a.aligned _
  alphaFit:=a.fit (.scalar .alpha)
  boundaryFit:=a.fit .boundary
  vectorFit:=by intro f; simpa only [(update_fields (n:=n) (e:=e) (w:=w) f).1,(update_fields (n:=n) (e:=e) (w:=w) f).2] using a.fit (updateField f)
  vectorApart:=by
    intro f g different
    have ne : updateField f≠updateField g := by cases f <;> cases g <;> simp_all [updateField]
    simpa only [(update_fields (n:=n) (e:=e) (w:=w) f).1,(update_fields (n:=n) (e:=e) (w:=w) f).2,(update_fields (n:=n) (e:=e) (w:=w) g).1,(update_fields (n:=n) (e:=e) (w:=w) g).2] using
      a.apart (updateField f) (updateField g) ne
  alphaApart:=by
    intro f
    have ne : Field.scalar .alpha≠updateField f := by cases f <;> decide
    have h := a.apart (.scalar .alpha) (updateField f) ne
    rw [(update_fields (n:=n) (e:=e) (w:=w) f).1,(update_fields (n:=n) (e:=e) (w:=w) f).2] at h
    exact h
  boundaryApart:=by
    intro f
    have ne : Field.boundary≠updateField f := by cases f <;> decide
    have h := a.apart .boundary (updateField f) ne
    rw [(update_fields (n:=n) (e:=e) (w:=w) f).1,(update_fields (n:=n) (e:=e) (w:=w) f).2] at h
    exact h

def Layout.updateP (a : Layout n e w) : AffineUpdate.Arena n where
  base:=a.base
  coefficient:=a.offset (.scalar .beta)
  direction:=a.offset .p
  shift:=a.offset .z
  bytes:=a.bytes
  small:=a.small
  aligned:=a.baseAligned
  noWrap:=a.noWrap
  coefficientAligned:=a.aligned _
  directionAligned:=a.aligned _
  shiftAligned:=a.aligned _
  coefficientFit:=a.fit (.scalar .beta)
  directionFit:=a.fit .p
  shiftFit:=a.fit .z
  coefficientApart:=a.apart (.scalar .beta) .p (by decide)
  shiftApart:=a.apart .z .p (by decide)

end PtxTorchLean.Poisson.PTX.Host

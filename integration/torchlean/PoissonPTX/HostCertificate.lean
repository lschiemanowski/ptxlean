import PoissonPTX.HostCertificateDecode

namespace PtxTorchLean.Poisson.PTX.Host.Certificate

/-- The discrete equations use exactly the uploaded connectivity and binary64
coefficient values. They are not a recomputation of ideal quadrature tables. -/
def problem (a : Layout n e w) (initial : Memory) (connected : a.Connectivity initial)
    (v : Values n w) : Poisson.Certificate.Problem e w n where
  mesh := ⟨fun cell i j =>
    let slot := Poisson.Certificate.Input.index (Poisson.Certificate.Input.index cell i) j
    ⟨(read32 initial (a.slot .cells+slot.val*4)).toNat,connected slot.val slot.isLt⟩⟩
  b := Poisson.matrix (fun i j => v.b (i,j))
  d := Poisson.matrix (fun i j => v.d (i,j))
  w := Poisson.matrix (fun i j => v.weights (i,j))
  rhs := v.rhs
  boundary := fun i => read32 initial (a.slot .boundary+i.val*4) != 0
  rtol := v.rtol
  atol := v.atol

/-- The exact acceptance gate reruns the represented equations over rationals.
It rejects nonfinite decoding, nonzero boundary x and excessive fresh residual.
No reported norm or convergence flag is trusted by this computation. -/
def accept (a : Layout n e w) (initial final : Memory) (connected : a.Connectivity initial) : Bool :=
  match decode a initial final with
  | none => false
  | some values => Poisson.Certificate.check (problem a initial connected values) values.solution

theorem accept_sound (accepted : accept a initial final connected=true) :
    ∃ values, decode a initial final=some values ∧ Represents a initial final values ∧
      (∀ i, (problem a initial connected values).boundary i=true → values.solution i=0) ∧
      Poisson.Certificate.realNorm (Poisson.Certificate.residual (problem a initial connected values) values.solution)≤
        max (values.atol : ℝ) ((values.rtol : ℝ)*Poisson.Certificate.realNorm
          (fun i => if (problem a initial connected values).boundary i then 0 else values.rhs i)) := by
  cases decoded : decode a initial final with
  | none => simp [accept,decoded] at accepted
  | some values =>
    have checked : Poisson.Certificate.check (problem a initial connected values) values.solution=true := by
      simpa only [accept,decoded] using accepted
    have result := Poisson.Certificate.certified_residual (problem a initial connected values) values.solution checked
    exact ⟨values,rfl,decode_sound decoded,result⟩

/-- Exact real-valued meaning of every returned solution coordinate follows
from its actual stored word, not from a separately supplied vector. -/
theorem Represents.solution_real {n e w : Nat} {a : Layout n e w}
    {initial final : Memory} {values : Values n w}
    (represented : Represents a initial final values) (i : Fin n) :
    (values.solution i : ℝ)=
      (FloatLib.Floats.Formats.BinaryInterchange.Model.ofBits (vectorWords a final .x i) :
        FloatLib.Floats.Formats.BinaryInterchange.Model FloatLib.Floats.Formats.BinaryInterchange.FloatFormat.binary64).toReal :=
  Poisson.Certificate.Input.decodeWord_real _ _ (represented.solution i)

end PtxTorchLean.Poisson.PTX.Host.Certificate

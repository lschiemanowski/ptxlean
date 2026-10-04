import PoissonPTX.HostLaunch

namespace PtxTorchLean.Poisson.PTX.Host

/-- Uploaded data that all solver stages must preserve. Working vectors and
computed status scalars are the only mutable named buffers. -/
def Field.mutable : Field → Bool
  | .x | .rhs | .r | .z | .p | .ap | .trueR | .applied | .element => true
  | .scalar .rtol | .scalar .atol => false
  | .scalar _ => true
  | _ => false

def Layout.Static (a : Layout n e w) (initial memory : Memory) : Prop :=
  ∀ f, f.mutable=false → ∀ byte,
    a.slot f≤byte → byte<a.slot f+f.count n e w*f.width → memory byte=initial byte

/-- A byte-level output frame, expressed using the common allocation's names. -/
def Layout.Writes (a : Layout n e w) (fields : List Field) (memory output : Memory) : Prop :=
  ∀ byte, (∀ f∈fields, byte<a.slot f ∨ a.slot f+f.count n e w*f.width≤byte) → output byte=memory byte

variable {n e w : Nat} {a : Layout n e w}

theorem Layout.static_refl (a : Layout n e w) (memory : Memory) : a.Static memory memory := by
  intro f static byte lo hi; rfl

theorem Layout.static_trans (first : a.Static initial middle) (second : a.Static middle final) :
    a.Static initial final := by
  intro f static byte lo hi
  exact (second f static byte lo hi).trans (first f static byte lo hi)

/-- The no-overlap layout makes every actual working-buffer write preserve
all static bytes. This says nothing about their values and needs no oracle. -/
theorem Layout.Writes.static (written : a.Writes fields memory output)
    (mutable : ∀ f∈fields, f.mutable=true) : a.Static memory output := by
  intro f static byte lo hi
  apply written byte
  intro g member
  have ne : g≠f := by intro same; have h := mutable g member; rw [same,static] at h; contradiction
  have apart := a.apart f g (Ne.symm ne)
  unfold Layout.slot at lo hi ⊢
  omega

def VectorEntry.writes : VectorEntry → List Field
  | .initialize => [.rhs,.r,.z,.p,.x]
  | .updateXRZ => [.x,.r,.z]
  | .updateP => [.p]
  | .restart => [.r,.z,.p]
  | .residual => [.trueR]
  | .assembly probe => [assemblyOutput probe]

def ScalarEntry.writes : ScalarEntry → List Scalar.Field
  | .start => [.rhsNorm,.residual,.tolerance,.active,.broken]
  | .alpha => [.broken,.useStep,.alpha]
  | .beta => [.broken,.beta,.rho,.active]
  | .norm => [.residual]
  | .restart => [.active]

theorem vector_writes_mutable (kind : VectorEntry) : ∀ f∈kind.writes, f.mutable=true := by
  cases kind <;> simp [VectorEntry.writes,Field.mutable,assemblyOutput]
  case assembly probe => cases probe <;> simp

theorem scalar_writes_mutable (kind : ScalarEntry) :
    ∀ f∈kind.writes.map Field.scalar, f.mutable=true := by
  cases kind <;> simp [ScalarEntry.writes,Field.mutable]

end PtxTorchLean.Poisson.PTX.Host

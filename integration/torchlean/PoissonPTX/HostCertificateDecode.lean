import PoissonPTX.HostKernelLaunch
import PoissonResidualInput

namespace PtxTorchLean.Poisson.PTX.Host.Certificate

/-- Decode each actual binary64 word exactly. Nonfinite words reject the
request; zero below is unreachable in an accepted decoded value. -/
def decodeWords {I : Type} [Fintype I] (bits : I → Word) : Option (I → ℚ) :=
  if ∀ i, (Poisson.Certificate.Input.decodeWord (bits i)).isSome=true then
    some (fun i => (Poisson.Certificate.Input.decodeWord (bits i)).getD 0)
  else none

theorem decodeWords_sound {I : Type} [Fintype I] {bits : I → Word} {values : I → ℚ}
    (decoded : decodeWords bits=some values) :
    ∀ i, Poisson.Certificate.Input.decodeWord (bits i)=some (values i) := by
  unfold decodeWords at decoded
  split at decoded
  · rename_i finite
    cases decoded
    intro i
    have h := finite i
    cases value : Poisson.Certificate.Input.decodeWord (bits i) with
    | none => simp [value] at h
    | some q => simp [value]
  · cases decoded

structure Values (nodes width : Nat) where
  b : Fin width × Fin width → ℚ
  d : Fin width × Fin width → ℚ
  weights : Fin width × Fin width → ℚ
  rhs : Fin nodes → ℚ
  solution : Fin nodes → ℚ
  rtol : ℚ
  atol : ℚ

def matrixWords (a : Layout n e w) (memory : Memory) (field : Field) (i : Fin w × Fin w) : Word :=
  read64 memory (a.slot field+(i.1.val*w+i.2.val)*8)

def vectorWords (a : Layout n e w) (memory : Memory) (field : Field) (i : Fin n) : Word :=
  read64 memory (a.slot field+i.val*8)

/-- All problem words come from uploaded memory; only x comes from the final
actual solver publication. This binds certification to the returned solution. -/
def decode (a : Layout n e w) (initial final : Memory) : Option (Values n w) := do
  let b ← decodeWords (matrixWords a initial .b)
  let d ← decodeWords (matrixWords a initial .d)
  let weights ← decodeWords (matrixWords a initial .w)
  let rhs ← decodeWords (vectorWords a initial .load)
  let solution ← decodeWords (vectorWords a final .x)
  let rtol ← Poisson.Certificate.Input.decodeWord (read64 initial (a.slot (.scalar .rtol)))
  let atol ← Poisson.Certificate.Input.decodeWord (read64 initial (a.slot (.scalar .atol)))
  return ⟨b,d,weights,rhs,solution,rtol,atol⟩

/-- Exact input/output-word meaning, with no residual or accuracy premise. -/
structure Represents (a : Layout n e w) (initial final : Memory) (v : Values n w) : Prop where
  b : ∀ i, Poisson.Certificate.Input.decodeWord (matrixWords a initial .b i)=some (v.b i)
  d : ∀ i, Poisson.Certificate.Input.decodeWord (matrixWords a initial .d i)=some (v.d i)
  weights : ∀ i, Poisson.Certificate.Input.decodeWord (matrixWords a initial .w i)=some (v.weights i)
  rhs : ∀ i, Poisson.Certificate.Input.decodeWord (vectorWords a initial .load i)=some (v.rhs i)
  solution : ∀ i, Poisson.Certificate.Input.decodeWord (vectorWords a final .x i)=some (v.solution i)
  rtol : Poisson.Certificate.Input.decodeWord (read64 initial (a.slot (.scalar .rtol)))=some v.rtol
  atol : Poisson.Certificate.Input.decodeWord (read64 initial (a.slot (.scalar .atol)))=some v.atol

theorem decode_sound (decoded : decode a initial final=some values) : Represents a initial final values := by
  simp only [decode,bind,Option.bind_eq_some_iff,pure] at decoded
  obtain ⟨b,hb,d,hd,weights,hw,rhs,hr,solution,hx,rtol,hrt,atol,hat,last⟩ := decoded
  cases last
  exact ⟨decodeWords_sound hb,decodeWords_sound hd,decodeWords_sound hw,decodeWords_sound hr,decodeWords_sound hx,hrt,hat⟩

end PtxTorchLean.Poisson.PTX.Host.Certificate

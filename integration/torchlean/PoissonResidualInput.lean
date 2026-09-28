import PoissonResidualCertificate
import FloatLib.Floats.Formats.BinaryInterchange.Model.RealSemantics
import FloatLib.Floats.Formats.BinaryInterchange.Format.Catalog
import Lean

/-! Exact, finite binary64 input decoding. The same wire words used by the GPU
are converted through FloatLib's dyadic semantics, not decimal approximations. -/
namespace PtxTorchLean.Poisson.Certificate.Input
open Lean TorchLean Correspondence
open FloatLib.Floats.Formats.BinaryInterchange (Model FloatFormat)

def decodeWord (word : BitVec 64) : Option ℚ :=
  ((Model.ofBits word : Model FloatFormat.binary64).toDyadic?).map FloatLib.Numerics.Dyadic.toRat

theorem decodeWord_real (word : BitVec 64) (q : ℚ) (h : decodeWord word = some q) :
    (q : ℝ) = (Model.ofBits word : Model FloatFormat.binary64).toReal := by
  unfold decodeWord at h
  cases hd : (Model.ofBits word : Model FloatFormat.binary64).toDyadic? with
  | none => simp [hd] at h
  | some d =>
    simp only [hd, Option.map_some, Option.some.injEq] at h
    rw [← h, FloatLib.Numerics.Dyadic.cast_toRat, Model.toReal_eq, hd]

def decode (j : Json) : Except String ℚ := do
  let n ← j.getNat?
  if n ≥ 2^64 then throw "binary64 word exceeds 64 bits"
  match decodeWord (BitVec.ofNat 64 n) with
  | none => throw "nonfinite binary64 word"
  | some q => return q

private def field (j : Json) (name : String) : Except String Json := j.getObjVal? name
private def natField (j : Json) (name : String) : Except String Nat := do (← field j name).getNat?
private def words (j : Json) (name : String) : Except String (Array ℚ) := do
  (← (← field j name).getArr?).mapM decode

/-- Shape validation returns bounded lookups; there is no out-of-range default. -/
def sized (xs : Array α) (n : Nat) : Except String (Fin n → α) :=
  if h : xs.size = n then .ok (fun i => xs[i.val]'(by omega))
  else .error s!"expected length {n}, got {xs.size}"

def index (i : Fin m) (j : Fin n) : Fin (m*n) :=
  ⟨i.val*n+j.val,by
    have h := Nat.mul_le_mul_right n (Nat.succ_le_of_lt i.isLt)
    simp only [Nat.succ_mul] at h
    have hj := j.isLt
    omega⟩

abbrev Request := Σ e n v, Problem e n v × (Fin v → ℚ)

/-- The wire format fixes the uniform-square dimensions and carries exact
connectivity and coefficient words from the GPU arena. -/
def parse (j : Json) : Except String Request := do
  let side ← natField j "n"
  let degree ← natField j "degree"
  if side == 0 || degree < 1 || degree > 4 then throw "expected positive n and degree 1..4"
  let m := degree+1
  let width := side*degree+1
  let v := width*width
  let e := side*side
  let cellsJson ← (← field j "cells").getArr?
  let cells ← cellsJson.mapM fun value => do
    let k ← value.getNat?
    if h : k < v then pure (⟨k,h⟩ : Fin v) else throw "cell node outside mesh"
  let cells ← sized cells ((e*m)*m)
  let b ← sized (← words j "B") (m*m)
  let d ← sized (← words j "D") (m*m)
  let w ← sized (← words j "W") (m*m)
  let rhs ← sized (← words j "load") v
  let x ← sized (← words j "solution") v
  let rtol ← decode (← field j "rtol")
  let atol ← decode (← field j "atol")
  let mesh : Connectivity e m v := ⟨fun element i j => cells (index (index element i) j)⟩
  -- Reject a different mesh even when its indices are in range.
  for element in List.finRange e do
    for i in List.finRange m do
      for k in List.finRange m do
        let expected := (element.val/side*degree+i.val)*width+element.val%side*degree+k.val
        if (mesh.node element i k).val != expected then throw "nonuniform connectivity"
  let p : Problem e m v := {
    mesh := mesh
    b := matrix fun i j => b (index i j)
    d := matrix fun i j => d (index i j)
    w := matrix fun i j => w (index i j)
    rhs := rhs
    boundary := fun i => i.val%width == 0 || i.val%width == width-1 || i.val/width == 0 || i.val/width == width-1
    rtol := rtol, atol := atol }
  return ⟨e,m,v,p,x⟩

/-- Public acceptance predicate over the exact serialized request. -/
def acceptedRequest (j : Json) : Bool :=
  match parse j with
  | .error _ => false
  | .ok ⟨_,_,_,p,x⟩ => check p x

/-- Parsing and the executable gate lead to the certified mathematical result,
not merely to agreement with a reported residual scalar. -/
theorem acceptedRequest_sound (j : Json) (h : acceptedRequest j = true) :
    ∃ (e n v : Nat) (p : Problem e n v) (x : Fin v → ℚ),
      parse j = .ok ⟨e,n,v,p,x⟩ ∧
      (∀ i, p.boundary i = true → x i = 0) ∧
      realNorm (residual p x) ≤
        max (p.atol : ℝ) ((p.rtol : ℝ) * realNorm (fun i => if p.boundary i then 0 else p.rhs i)) := by
  cases hp : parse j with
  | error error => simp [acceptedRequest,hp] at h
  | ok request =>
    rcases request with ⟨e,n,v,p,x⟩
    exact ⟨e,n,v,p,x,rfl,certified_residual p x (by simpa [acceptedRequest,hp] using h)⟩

private def rational (q : ℚ) : Json := Json.mkObj [
  ("numerator",toJson (toString q.num)),("denominator",toJson (toString q.den))]

/-- Evaluation returns only an exact check outcome; floating residual estimates
are not inputs to the check. -/
def evaluate (request : Request) : Json :=
  let ⟨_,_,_,p,x⟩ := request
  Json.mkObj [
    ("accepted",toJson (check p x)),
    ("residual_squared",rational (computedSquare p x)),
    ("threshold_squared",rational (thresholdSquare p)),
    ("claim",toJson "Exact residual bound for represented coefficient tables; zero boundary; no PDE or instruction-trace claim.")]

end PtxTorchLean.Poisson.Certificate.Input

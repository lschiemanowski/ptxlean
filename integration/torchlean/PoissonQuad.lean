import NN.Spec.Core.Tensor.Linalg

/-! Executable Q1–Q4 unit-square Poisson reference. Native binary64 execution
and generic tensor algebra; no PDE, rounding-error or PTX refinement claim. -/
namespace PtxTorchLean.Poisson
open TorchLean

abbrev Mat (α : Type) [Storage α] (m n : Nat) := Tensor α [m,n]

def matrix [Storage α] (f : Fin m → Fin n → α) : Mat α m n :=
  Tensor.Internal.Rep.ofFn fun ij => f ij.1 ij.2.1

def transpose [Storage α] (a : Mat α m n) : Mat α n m :=
  matrix fun i j => Spec.get2 a j i

def hadamard [Storage α] [Mul α] (a b : Mat α m n) : Mat α m n :=
  matrix fun i j => Spec.get2 a i j * Spec.get2 b i j

def plus [Storage α] [Add α] (a b : Mat α m n) : Mat α m n :=
  matrix fun i j => Spec.get2 a i j + Spec.get2 b i j

/-- Two one-coordinate contractions per gradient, followed by their transposes.
The same definition can be instantiated with Float or with exact real numbers. -/
def localAction [Storage α] [Add α] [Mul α] [Zero α]
    (b d : Mat α q m) (w : Mat α q q) (u : Mat α m m) : Mat α m m :=
  let dx := Spec.matMulSpec (Spec.matMulSpec b u) (transpose d)
  let dy := Spec.matMulSpec (Spec.matMulSpec d u) (transpose b)
  plus (Spec.matMulSpec (Spec.matMulSpec (transpose b) (hadamard w dx)) d)
       (Spec.matMulSpec (Spec.matMulSpec (transpose d) (hadamard w dy)) b)

def localLoad [Storage α] [Add α] [Mul α] [Zero α]
    (b : Mat α q m) (w f : Mat α q q) : Mat α m m :=
  Spec.matMulSpec (Spec.matMulSpec (transpose b) (hadamard w f)) b

/-- Explicit zero boundary extension, independently of scalar precision. -/
def zeroBoundary [Zero α] (boundary : Fin n → Bool) (u : Fin n → α) (i : Fin n) : α :=
  if boundary i then 0 else u i

theorem zeroBoundary_boundary [Zero α] (boundary : Fin n → Bool) (u : Fin n → α)
    (i : Fin n) (h : boundary i = true) : zeroBoundary boundary u i = 0 := by
  simp [zeroBoundary,h]

theorem zeroBoundary_interior [Zero α] (boundary : Fin n → Bool) (u : Fin n → α)
    (i : Fin n) (h : boundary i = false) : zeroBoundary boundary u i = u i := by
  simp [zeroBoundary,h]

private def pi : Float := 3.141592653589793
private def sum (xs : Array Float) : Float := xs.foldl (· + ·) 0
private def tab (n : Nat) (f : Nat → α) : Array α := (Array.range n).map f
private def mm [Storage α] (a : Mat α m n) (i j : Nat) (fallback : α) : α :=
  if hi : i < m then if hj : j < n then Spec.get2 a ⟨i,hi⟩ ⟨j,hj⟩ else fallback else fallback

def sineSolution (x y : Float) : Float := (pi*x).sin * (pi*y).sin
def sineSource (x y : Float) : Float := 2*pi*pi*sineSolution x y
def sineGradient (x y : Float) : Float × Float :=
  (pi*(pi*x).cos*(pi*y).sin, pi*(pi*x).sin*(pi*y).cos)

def lobattoNodes (degree : Nat) : Except String (Array Float) := do
  let raw ← match degree with
    | 1 => pure #[-1,1]
    | 2 => pure #[-1,0,1]
    | 3 => let a := 1/(5.0).sqrt; pure #[-1,-a,a,1]
    | 4 => let a := (3.0/7).sqrt; pure #[-1,-a,0,a,1]
    | _ => throw "degree must be one through four"
  return raw.map fun x => (x+1)/2

/-- Legendre polynomial and derivative by recurrence; no derivative division at roots. -/
private def legendre (n : Nat) (x : Float) : Float × Float := Id.run do
  if n == 0 then return (1,0)
  let mut prev := 1.0; let mut cur := x
  let mut dprev := 0.0; let mut dcur := 1.0
  for k in [2:n+1] do
    let kf := Float.ofNat k
    let next := ((2*kf-1)*x*cur-(kf-1)*prev)/kf
    let dn := ((2*kf-1)*(cur+x*dcur)-(kf-1)*dprev)/kf
    prev := cur; cur := next; dprev := dcur; dcur := dn
  return (cur,dcur)

/-- Setup for the two-to-six-point rules used by Q1–Q4 (also accepts one).
Each root has at most 64 Newton steps and is checked before acceptance. -/
def gaussRule (count : Nat) : Except String (Array Float × Array Float) := do
  if count == 0 || count > 6 then throw "quadrature count must be one through six"
  let mut points := #[]; let mut weights := #[]
  for i in [0:count] do
    let mut z := -(pi*(Float.ofNat i+0.75)/(Float.ofNat count+0.5)).cos
    let mut done := false
    for _ in [0:64] do
      if !done then
        let (v,d) := legendre count z
        let next := z-v/d
        done := (next-z).abs ≤ 1e-15
        z := next
    let (v,d) := legendre count z
    let w := 1/((1-z*z)*d*d)
    if !done || !z.isFinite || !w.isFinite || !(w > 0) || !(z.abs < 1) || v.abs > 2e-14 then
      throw "quadrature root calculation failed"
    points := points.push ((z+1)/2); weights := weights.push w
  return (points,weights)

/-- Product-rule tabulation also works at interpolation nodes. -/
def lagrangeBasis (nodes points : Array Float) :
    Mat Float points.size nodes.size × Mat Float points.size nodes.size := Id.run do
  let entry := fun (q : Fin points.size) (i : Fin nodes.size) => Id.run do
    let mut value := 1.0; let mut derivative := 0.0
    for j in [0:nodes.size] do
      if j != i.val then
        value := value * (points[q]-nodes[j]!) / (nodes[i]-nodes[j]!)
        let mut term := 1/(nodes[i]-nodes[j]!)
        for k in [0:nodes.size] do
          if k != i.val && k != j then
            term := term * (points[q]-nodes[k]!) / (nodes[i]-nodes[k]!)
        derivative := derivative + term
    return (value,derivative)
  return (matrix fun q i => (entry q i).1, matrix fun q i => (entry q i).2)

structure Mesh where
  n : Nat
  degree : Nat
  points : Array (Float × Float)
  cells : Array (Array Nat)
  boundary : Array Bool
  interior : Array Nat
  deriving Inhabited

def quadrilateralSquare (n degree : Nat) : Except String Mesh := do
  if n == 0 then throw "n must be positive"
  let nodes ← lobattoNodes degree
  let width := n*degree+1
  let axis := tab width fun i => if i == n*degree then 1 else
    (Float.ofNat (i/degree)+nodes[i%degree]!)/Float.ofNat n
  let points := tab (width*width) fun i => (axis[i%width]!,axis[i/width]!)
  let boundary := tab points.size fun i => i%width == 0 || i%width == width-1 || i/width == 0 || i/width == width-1
  let cells := tab (n*n) fun e => tab ((degree+1)*(degree+1)) fun i =>
    (e/n*degree+i/(degree+1))*width+e%n*degree+i%(degree+1)
  return ⟨n,degree,points,cells,boundary,(Array.range points.size).filter fun i => !boundary[i]!⟩

structure Operator where
  mesh : Mesh
  nodes : Array Float
  q : Array Float
  weights : Array Float
  b : Mat Float q.size nodes.size
  d : Mat Float q.size nodes.size
  w : Mat Float q.size q.size
  diagonal : Array Float

private def scatter (cells : Array (Array Nat)) (locals : Array (Array Float)) (size : Nat) : Array Float := Id.run do
  let mut out := Array.replicate size 0.0
  for e in [0:cells.size] do
    for i in [0:cells[e]!.size] do
      let j := (cells[e]!)[i]!
      out := out.set! j (out[j]!+(locals[e]!)[i]!)
  return out

private def flatten (a : Mat Float m n) : Array Float :=
  tab (m*n) fun i => mm a (i/n) (i%n) 0

/-- Construction is through mesh parameters, not independently deformable geometry. -/
def makeOperator (n degree : Nat) : Except String Operator := do
  let mesh ← quadrilateralSquare n degree
  let nodes ← lobattoNodes degree
  let (q,weights) ← gaussRule (degree+1)
  let (b,d) := lagrangeBasis nodes q
  let w := matrix fun (i : Fin q.size) (j : Fin q.size) => weights[i.val]! * weights[j.val]!
  let mass := tab nodes.size fun i => sum (tab q.size fun k => weights[k]! * (mm b k i 0)^2)
  let stiff := tab nodes.size fun i => sum (tab q.size fun k => weights[k]! * (mm d k i 0)^2)
  let diag := tab (nodes.size*nodes.size) fun i =>
    mass[i/nodes.size]! * stiff[i%nodes.size]! + stiff[i/nodes.size]! * mass[i%nodes.size]!
  let diagonal := scatter mesh.cells (Array.replicate mesh.cells.size diag) mesh.points.size
  if !(mesh.interior.all fun i => diagonal[i]!.isFinite && diagonal[i]! > 0) then
    throw "interior diagonal must be finite and positive"
  return ⟨mesh,nodes,q,weights,b,d,w,diagonal⟩

private def checkVector (values : Array Float) (size : Nat) : Except String Unit := do
  if values.size != size then throw s!"expected vector of length {size}, got {values.size}"
  if !(values.all Float.isFinite) then throw "vector must be finite"

/-- The local cell view used by the operator; public for instruction correspondence. -/
def gather (o : Operator) (values : Array Float) (e : Nat) : Mat Float o.nodes.size o.nodes.size :=
  matrix fun i j => values[(o.mesh.cells[e]!)[i.val*o.nodes.size+j.val]!]!

private def applyRaw (o : Operator) (values : Array Float) : Array Float :=
  scatter o.mesh.cells (tab o.mesh.cells.size fun e => flatten (localAction o.b o.d o.w (gather o values e))) o.mesh.points.size

def apply (o : Operator) (values : Array Float) : Except String (Array Float) := do
  checkVector values o.mesh.points.size
  return applyRaw o values

private def restrict (o : Operator) (values : Array Float) : Array Float :=
  o.mesh.interior.map fun i => values[i]!

private def extend (o : Operator) (values : Array Float) : Array Float := Id.run do
  let mut full := Array.replicate o.mesh.points.size 0.0
  for k in [0:o.mesh.interior.size] do full := full.set! o.mesh.interior[k]! values[k]!
  return Array.ofFn fun (i : Fin o.mesh.points.size) =>
    zeroBoundary (fun j => o.mesh.boundary[j.val]!) (fun j => full[j.val]!) i

private def applyInteriorRaw (o : Operator) (values : Array Float) : Array Float :=
  restrict o (applyRaw o (extend o values))

def applyInterior (o : Operator) (values : Array Float) : Except String (Array Float) := do
  checkVector values o.mesh.interior.size
  return applyInteriorRaw o values

private def quadraturePoint (mesh : Mesh) (q : Array Float) (e i j : Nat) : Float × Float :=
  let origin := mesh.points[(mesh.cells[e]!)[0]!]!
  (origin.1+q[j]!/Float.ofNat mesh.n,origin.2+q[i]!/Float.ofNat mesh.n)

def load (o : Operator) (source : Float → Float → Float := sineSource) : Except String (Array Float) := do
  let mut locals := #[]
  for e in [0:o.mesh.cells.size] do
    let f := matrix fun (i : Fin o.q.size) (j : Fin o.q.size) =>
      let xy := quadraturePoint o.mesh o.q e i.val j.val
      source xy.1 xy.2
    if !((flatten f).all Float.isFinite) then throw "source must be finite"
    locals := locals.push ((flatten (localLoad o.b o.w f)).map fun x => x/(Float.ofNat o.mesh.n)^2)
  return scatter o.mesh.cells locals o.mesh.points.size

structure Options where
  rtol : Float := 1e-10
  atol : Float := 0
  maxiter : Nat := 1000
  checkEvery : Nat := 10
  deriving Inhabited

inductive Reason where
  | converged | breakdown | maxiter
  deriving BEq, Repr, Inhabited

structure Result where
  solution : Array Float
  reason : Reason
  iterations : Nat
  residualNorm : Float
  relativeResidual : Float
  tolerance : Float
  deriving Inhabited

private def dot (a b : Array Float) : Float := sum (tab a.size fun i => a[i]!*b[i]!)
private def norm (a : Array Float) : Float := (dot a a).sqrt
private def combine (a : Array Float) (s : Float) (b : Array Float) : Array Float :=
  tab a.size fun i => a[i]!+s*b[i]!

/-- Bounded PCG, including frozen steps, true-residual checks and restart.
Success is a measured residual criterion, not a PDE-error certificate. -/
def solvePCG (o : Operator) (rhsFull : Array Float) (opts : Options := {}) : Except String Result := do
  checkVector rhsFull o.mesh.points.size
  if !opts.rtol.isFinite || !opts.atol.isFinite || opts.rtol < 0 || opts.atol < 0 ||
      (opts.rtol == 0 && opts.atol == 0) || opts.checkEvery == 0 then throw "invalid solver options"
  let rhs := restrict o rhsFull
  let rhsNorm := norm rhs
  let tolerance := max opts.atol (opts.rtol*rhsNorm)
  let finish := fun x it residual reason =>
    Result.mk (extend o x) reason it residual (if rhsNorm == 0 then 0 else residual/rhsNorm) tolerance
  let mut x := Array.replicate rhs.size 0.0
  if !rhsNorm.isFinite then return finish x 0 rhsNorm .breakdown
  if rhsNorm ≤ tolerance then return finish x 0 rhsNorm .converged
  if opts.maxiter == 0 then return finish x 0 rhsNorm .maxiter
  let diagonal := restrict o o.diagonal
  let precondition := fun r => tab rhs.size fun i => r[i]!/diagonal[i]!
  let mut r := rhs
  let mut z := precondition r
  let mut p := z
  let mut rho := dot r z
  let mut active := true; let mut broken := false
  let mut residualNorm := rhsNorm
  for it in [1:opts.maxiter+1] do
    let ap := applyInteriorRaw o p
    let denominator := dot p ap
    let valid := denominator.isFinite && denominator > 0 && rho.isFinite && rho > 0
    broken := broken || (active && !valid)
    let useStep := active && valid
    let alpha := if useStep then rho/denominator else 0
    x := combine x alpha p
    r := combine r (-alpha) ap
    z := precondition r
    let rhoNext := dot r z
    broken := broken || (active && !rhoNext.isFinite)
    let beta := if useStep then rhoNext/(if rho > 0 then rho else 1) else 0
    p := combine z beta p
    rho := rhoNext
    active := useStep && dot r r > tolerance*tolerance && !broken
    if it % opts.checkEvery == 0 || it == opts.maxiter then
      let trueResidual := combine rhs (-1) (applyInteriorRaw o x)
      residualNorm := norm trueResidual
      if !residualNorm.isFinite then return finish x it residualNorm .breakdown
      if residualNorm ≤ tolerance then return finish x it residualNorm .converged
      if broken then return finish x it residualNorm .breakdown
      if !active then
        r := trueResidual; z := precondition r; p := z; rho := dot r z; active := true
  return finish x opts.maxiter residualNorm .maxiter

/-- Numerical L2 and gradient-seminorm estimates, using degree+2 quadrature. -/
def errorNorms (o : Operator) (solution : Array Float)
    (exact : Float → Float → Float := sineSolution)
    (gradient : Float → Float → Float × Float := sineGradient) : Except String (Float × Float) := do
  checkVector solution o.mesh.points.size
  let (q,weights) ← gaussRule (o.mesh.degree+2)
  let (b,d) := lagrangeBasis o.nodes q
  let mut l2 := 0.0; let mut h1 := 0.0
  for e in [0:o.mesh.cells.size] do
    let u := gather o solution e
    let value := Spec.matMulSpec (Spec.matMulSpec b u) (transpose b)
    let dx := Spec.matMulSpec (Spec.matMulSpec b u) (transpose d)
    let dy := Spec.matMulSpec (Spec.matMulSpec d u) (transpose b)
    for i in [0:q.size] do
      for j in [0:q.size] do
        let (x,y) := quadraturePoint o.mesh q e i j
        let grad := gradient x y
        let ev := mm value i j 0-exact x y
        let ex := Float.ofNat o.mesh.n*mm dx i j 0-grad.1
        let ey := Float.ofNat o.mesh.n*mm dy i j 0-grad.2
        let w := weights[i]!*weights[j]!/(Float.ofNat o.mesh.n)^2
        l2 := l2+w*ev*ev; h1 := h1+w*(ex*ex+ey*ey)
  if !l2.isFinite || !h1.isFinite then throw "nonfinite error integral"
  return (l2.sqrt,h1.sqrt)

end PtxTorchLean.Poisson

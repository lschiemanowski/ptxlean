import PoissonPTX.HostSchedule
import PoissonPTX.InitializeArena
import PoissonPTX.RestartVectorsArena
import PoissonPTX.UpdateXRZArena
import PoissonPTX.AffineUpdateArena
import PoissonPTX.FreshResidualArena

namespace PtxTorchLean.Poisson.PTX.Host

/-- Names of the one persistent allocation's buffers. Scalar control fields
retain their existing four-byte/eight-byte widths. -/
inductive Field where
  | b | d | w | cells | boundary | offsets | entries | load | diagonal | probe
  | x | rhs | r | z | p | ap | trueR | applied | element
  | scalar (field : Scalar.Field)
  deriving DecidableEq, Repr

def Field.width : Field → Nat
  | .cells | .boundary | .offsets | .entries => 4
  | .scalar field => field.width
  | _ => 8

def Field.count (nodes cells width : Nat) : Field → Nat
  | .b | .d | .w => width*width
  | .cells | .entries | .element => cells*width*width
  | .offsets => nodes+1
  | .scalar _ => 1
  | _ => nodes

/-- Buffer extents, alignment and separation describe physical storage only.
The global allocation is shared by every launch; no computed value is a field. -/
structure Layout (nodes cells width : Nat) where
  base : Word
  bytes : Nat
  offset : Field → Word
  small : nodes < 2^30
  localSmall : cells*width*width < 2^30
  lo : 2≤width
  hi : width≤5
  baseAligned : base.toNat%8=0
  aligned : ∀ f, (offset f).toNat%8=0
  noWrap : base.toNat+bytes≤2^64
  fit : ∀ f, (offset f).toNat+f.count nodes cells width*f.width≤bytes
  apart : ∀ f g, f≠g →
    (offset f).toNat+f.count nodes cells width*f.width≤(offset g).toNat ∨
    (offset g).toNat+g.count nodes cells width*g.width≤(offset f).toNat

def Layout.slot (a : Layout n e w) (f : Field) : Nat := a.base.toNat+(a.offset f).toNat

theorem field_width (f : Field) : f.width=4 ∨ f.width=8 := by
  cases f <;> simp [Field.width]
  case scalar f => cases f <;> simp [Scalar.Field.width]

theorem Layout.align_width (a : Layout n e w) (f : Field) : (a.offset f).toNat%f.width=0 := by
  have aligned := a.aligned f
  rcases field_width f with h|h <;> rw [h] <;> omega

def Layout.scalar (a : Layout n e w) : Scalar.Arena where
  base:=a.base
  bytes:=a.bytes
  offset:=fun f => a.offset (.scalar f)
  baseAligned:=a.baseAligned
  aligned:=fun f => a.align_width (.scalar f)
  fit:=by intro f; simpa [Field.count,Field.width] using a.fit (.scalar f)
  noWrap:=a.noWrap
  apart:=by
    intro f g ne
    simpa [Field.count,Field.width] using a.apart (.scalar f) (.scalar g) (by simpa using ne)

/-- Project any distinct set of binary64 vector buffers into the existing
physical array arena, retaining the same boundary mask and allocation. -/
def Layout.arrays {Fields : Type} (a : Layout n e w) (fields : Fields → Field)
    (distinct : Function.Injective fields)
    (vectors : ∀ f, (fields f).count n e w=n ∧ (fields f).width=8 ∧ fields f≠.boundary) :
    ArrayArena Fields n where
  base:=a.base
  boundary:=a.offset .boundary
  vector:=fun f => a.offset (fields f)
  bytes:=a.bytes
  small:=a.small
  aligned:=a.baseAligned
  noWrap:=a.noWrap
  boundaryAligned:=a.align_width .boundary
  vectorAligned:=fun f => a.aligned (fields f)
  boundaryFit:=a.fit .boundary
  vectorFit:=by intro f; simpa only [(vectors f).1,(vectors f).2.1] using a.fit (fields f)
  vectorApart:=by
    intro f g ne
    simpa only [(vectors f).1,(vectors f).2.1,(vectors g).1,(vectors g).2.1] using
      a.apart (fields f) (fields g) (fun same => ne (distinct same))
  boundaryApart:=by
    intro f
    have h := a.apart .boundary (fields f) (Ne.symm (vectors f).2.2)
    rw [(vectors f).1,(vectors f).2.1] at h
    exact h

def initializeField : Initialize.Field → Field
  | .input => .load | .rhs => .rhs | .r => .r | .diagonal => .diagonal | .z => .z | .p => .p | .x => .x

def restartField : RestartVectors.Field → Field
  | .source => .trueR | .r => .r | .diagonal => .diagonal | .z => .z | .p => .p

def Layout.initialize (a : Layout n e w) : Initialize.Arena n :=
  a.arrays initializeField (by intro f g same; cases f <;> cases g <;> simp_all [initializeField])
    (by intro f; cases f <;> simp [initializeField,Field.count,Field.width])

def Layout.restart (a : Layout n e w) : RestartVectors.Arena n :=
  a.arrays restartField (by intro f g same; cases f <;> cases g <;> simp_all [restartField])
    (by intro f; cases f <;> simp [restartField,Field.count,Field.width])

def Layout.residual (a : Layout n e w) : FreshResidual.Arena n where
  base:=a.base
  rhs:=a.offset .rhs
  ap:=a.offset .ap
  output:=a.offset .trueR
  bytes:=a.bytes
  small:=a.small
  aligned:=a.baseAligned
  noWrap:=a.noWrap
  fields:=by
    intro off member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl|rfl|rfl
    all_goals exact ⟨a.aligned _,a.fit _⟩
  separated:=by
    intro off member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl|rfl
    · exact a.apart .trueR .rhs (by decide)
    · exact a.apart .trueR .ap (by decide)

end PtxTorchLean.Poisson.PTX.Host

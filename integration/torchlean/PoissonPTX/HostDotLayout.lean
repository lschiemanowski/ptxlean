import PoissonPTX.HostStorage
import PoissonPTX.DotPublishedComplete

namespace PtxTorchLean.Poisson.PTX.Host
open Concurrent

inductive DotEntry where
  | rhs | rz | pap | next | rr | trueResidual
  deriving DecidableEq, Repr

def DotEntry.entry : DotEntry → Entry
  | .rhs => .dotRhs | .rz => .dotRz | .pap => .dotPap
  | .next => .dotNext | .rr => .dotRR | .trueResidual => .dotTrue

def DotEntry.left : DotEntry → Field
  | .rhs => .rhs | .rz => .r | .pap => .p | .next => .r | .rr => .r | .trueResidual => .trueR

def DotEntry.right : DotEntry → Field
  | .rhs => .rhs | .rz => .z | .pap => .ap | .next => .z | .rr => .r | .trueResidual => .trueR

def DotEntry.output : DotEntry → Scalar.Field
  | .rhs => .rhsSquare | .rz => .rho | .pap => .denominator
  | .next => .rhoNext | .rr => .rr | .trueResidual => .trueSquare

theorem DotEntry.output_width (kind : DotEntry) : kind.output.width=8 := by
  cases kind <;> rfl

def Layout.dotContext (a : Layout n e w) (thread : Fin 256) : Kernel.Context :=
  ⟨a.base,BitVec.ofNat 32 thread.val,0⟩

/-- The reduction uses one full block and 2048 private shared bytes. Zero is a
valid model base in the separate shared address space. No shared value is assumed. -/
def Layout.dotStart (a : Layout n e w) (memory : Memory) (regs : Fin 256 → Registers) : NativeFlow.State 256 :=
  ⟨⟨fun t => {(a.flowStart memory (regs t)).core with sharedBytes:=2048},Ptx.Barrier.reset 0,none⟩,
    fun _ _ => false,fun _ => false⟩

def Layout.dotCode (a : Layout n e w) (kind : DotEntry) : List NativeFlow.Instr :=
  Dot.program n (a.offset kind.left) (a.offset kind.right) (a.offset (.scalar kind.output)) 0

theorem Layout.dot_lane (a : Layout n e w) (t : Fin 256) : (a.dotContext t).lane.toNat=t.val := by
  change t.val%2^32=t.val
  exact Nat.mod_eq_of_lt (by have := t.isLt; omega)

theorem Layout.dot_arrays (a : Layout n e w) (kind : DotEntry) (memory : Memory) (regs : Fin 256 → Registers) (t : Fin 256) :
    DotInput.Arrays (DotInput.setup (a.dotContext t) 0 (NativeFlow.lane (a.dotStart memory regs) t)).core n
      (a.offset kind.left) (a.offset kind.right) := by
  have values : ∀ f∈[kind.left,kind.right], (a.offset f).toNat%8=0 ∧ (a.offset f).toNat+n*8≤a.bytes := by
    intro f member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl|rfl
    · refine ⟨a.aligned _,?_⟩; cases kind <;> exact a.fit _
    · refine ⟨a.aligned _,?_⟩; cases kind <;> exact a.fit _
  change a.base.toNat=a.base.toNat ∧ a.base.toNat%8=0 ∧ a.base.toNat+a.bytes≤2^64 ∧ _
  refine ⟨rfl,a.baseAligned,a.noWrap,?_⟩
  intro off member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl|rfl
  · exact values kind.left (by simp)
  · exact values kind.right (by simp)

theorem Layout.dot_apart (a : Layout n e w) (kind : DotEntry) :
    Dot.OutputApart n (a.offset kind.left) (a.offset kind.right) (a.offset (.scalar kind.output)) := by
  intro off member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl|rfl
  all_goals cases kind
  all_goals first
    | exact a.apart (.scalar .rhsSquare) .rhs (by decide)
    | exact a.apart (.scalar .rho) .r (by decide)
    | exact a.apart (.scalar .rho) .z (by decide)
    | exact a.apart (.scalar .denominator) .p (by decide)
    | exact a.apart (.scalar .denominator) .ap (by decide)
    | exact a.apart (.scalar .rhoNext) .r (by decide)
    | exact a.apart (.scalar .rhoNext) .z (by decide)
    | exact a.apart (.scalar .rr) .r (by decide)
    | exact a.apart (.scalar .trueSquare) .trueR (by decide)

end PtxTorchLean.Poisson.PTX.Host

import PoissonPTX.ArrayArenaSafety
import PoissonPTX.InitializeAccess

namespace PtxTorchLean.Poisson.PTX.Initialize
open Concurrent

inductive Field where
  | input | rhs | r | diagonal | z | p | x
  deriving DecidableEq, Repr

abbrev Arena (n : Nat) := ArrayArena Field n

def Arena.program (a : Arena n) := entry (BitVec.ofNat 32 n) a.boundary (a.vector .input) (a.vector .rhs) (a.vector .r)
  (a.vector .diagonal) (a.vector .z) (a.vector .p) (a.vector .x)

theorem Arena.local_valid (a : Arena n) (memory : Memory) (regs : Registers) (i : Fin n) :
    Valid (Assembly.setup (a.context i) (BitVec.ofNat 32 n) (a.start memory regs)).core
      a.boundary (a.vector .input) (a.vector .rhs) (a.vector .r) (a.vector .diagonal) (a.vector .z) (a.vector .p) (a.vector .x) := by
  constructor
  · intro field member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with h|h|h|h|h|h|h <;> subst field
    all_goals exact a.vector_valid memory regs i _
  · exact a.boundary_valid memory regs i

theorem Arena.local_separate (a : Arena n) (memory : Memory) (regs : Registers) (i : Fin n) :
    Separate (Assembly.setup (a.context i) (BitVec.ofNat 32 n) (a.start memory regs)).core
      (a.vector .rhs) (a.vector .r) (a.vector .diagonal) (a.vector .z) (a.vector .p) (a.vector .x) := by
  constructor
  all_goals simp only [a.setup_address]
  all_goals exact a.owners _ _ i i (Or.inl (by decide))

variable {n : Nat} {a : Arena n} {memory : Memory} {regs : Fin n → Registers}
  {t : Fin n → Flow.State} {words : List (Event n)} {indices : List (Fin n × IndexSources.Access)}

theorem Arena.access_shape
    (shape : AccessAt (a.context thread) a.boundary (a.vector .input) (a.vector .rhs) (a.vector .r)
      (a.vector .diagonal) (a.vector .z) (a.vector .p) (a.vector .x) access) :
    access.space=.global ∧
    (if access.data.store then ∃ f, (f=Field.rhs ∨ f=Field.r ∨ f=Field.z ∨ f=Field.p ∨ f=Field.x) ∧ access.data.address=a.slot f thread
     else ∃ f, (f=Field.input ∨ f=Field.diagonal) ∧ access.data.address=a.slot f thread) := by
  unfold AccessAt at shape
  have addressEq (f : Field) : (address64 (a.context thread).arena (Kernel.Residual.index (a.context thread)) (a.vector f)).toNat=a.slot f thread := a.vector_address thread f
  simp only [addressEq] at shape
  refine ⟨shape.1,?_⟩
  by_cases writing : access.data.store=true
  · simp only [writing,↓reduceIte] at shape ⊢
    rcases shape.2 with hh|hr|hz|hp|hx
    · exact ⟨.rhs,by simp,hh.2⟩
    · exact ⟨.r,by simp,hr.2⟩
    · exact ⟨.z,by simp,hz.2⟩
    · exact ⟨.p,by simp,hp.2⟩
    · exact ⟨.x,by simp,hx.2⟩
  · simp only [writing] at shape ⊢
    rcases shape.2 with hs|hd
    · exact ⟨.input,by simp,hs.2⟩
    · exact ⟨.diagonal,by simp,hd.2⟩

theorem Arena.parallel_access
    (run : Flow.Parallel.Runs a.context a.program (fun i => a.start memory (regs i)) words indices t)
    (member : Event.data thread access∈words) :
    access.space=.global ∧
    (if access.data.store then ∃ f, (f=Field.rhs ∨ f=Field.r ∨ f=Field.z ∨ f=Field.p ∨ f=Field.x) ∧ access.data.address=a.slot f thread
     else ∃ f, (f=Field.input ∨ f=Field.diagonal) ∧ access.data.address=a.slot f thread) :=
  a.access_shape (accesses (Flow.Parallel.project run thread) (address_initial rfl) (Flow.Parallel.word_member.mpr member))

theorem Arena.parallel_index
    (run : Flow.Parallel.Runs a.context a.program (fun i => a.start memory (regs i)) words indices t)
    (member : (thread,access)∈indices) : access.address=a.base.toNat+a.boundary.toNat+thread.val*4 := by
  have shape := index_accesses (Flow.Parallel.project run thread) (address_initial rfl) (Flow.Parallel.index_member.mpr member)
  rw [shape.2]
  exact a.boundary_address thread

end PtxTorchLean.Poisson.PTX.Initialize

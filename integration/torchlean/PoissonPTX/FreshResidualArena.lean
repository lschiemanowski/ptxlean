import PoissonPTX.FreshResidualAccess

namespace PtxTorchLean.Poisson.PTX.FreshResidual
open Concurrent

/-- Reuse the existing residual layout, including permission for the two
read-only inputs to overlap. No unused boundary array is required. -/
abbrev Arena (n : Nat) := Weak.Residual.Parallel.Arena n

def Arena.context (a : Arena n) := Weak.Residual.Parallel.Arena.context a

def Arena.start (a : Arena n) (memory : Memory) (regs : Registers) : Flow.State :=
  ⟨{pc:=0,regs:=regs,global:=memory,shared:=fun _ => 0,globalStart:=a.base.toNat,
    globalBytes:=a.bytes,sharedStart:=0,sharedBytes:=0},fun _ => false,false⟩

def Arena.program (a : Arena n) := entry (BitVec.ofNat 32 n) a.rhs a.ap a.output

def Arena.slot (a : Arena n) (off : Word) (i : Fin n) := a.base.toNat+i.val*8+off.toNat

theorem Arena.live (a : Arena n) (i : Fin n) : Kernel.Residual.live (a.context i) (BitVec.ofNat 32 n) :=
  Weak.Residual.Parallel.Arena.live a i

theorem Arena.address (a : Arena n) (i : Fin n) (off : Word) (member : off∈[a.rhs,a.ap,a.output]) :
    (address64 a.base (Kernel.Residual.index (a.context i)) off).toNat=a.slot off i := by
  have result := Weak.Residual.Parallel.Arena.addr a (fun _ => 0) (fun _ _ => 0) i off member
  simpa only [Weak.Residual.Parallel.Inputs.addr,Weak.Residual.Parallel.Arena.inputs,
    Kernel.Residual.setup_address,Arena.context,Weak.Residual.Parallel.Arena.context,Arena.slot] using result

theorem Arena.valid (a : Arena n) (i : Fin n) (off : Word) (member : off∈[a.rhs,a.ap,a.output]) :
    Valid64 a.base.toNat a.bytes (address64 a.base (Kernel.Residual.index (a.context i)) off).toNat := by
  have result := (Weak.Residual.Parallel.Arena.inputs a (fun _ => 0) (fun _ _ => 0)).valid i off member
  simpa only [Weak.Residual.Parallel.Arena.inputs,Weak.Residual.Parallel.Arena.start,
    Kernel.Residual.setup_address,Arena.context,Weak.Residual.Parallel.Arena.context,Arena.slot] using result

theorem Arena.owners (a : Arena n) (i j : Fin n) (different : i≠j) :
    Sources.Disjoint (a.slot a.output i) (a.slot a.output j) := by
  unfold Sources.Disjoint Arena.slot
  have ne : i.val≠j.val := fun h => different (Fin.ext h)
  omega

theorem Arena.separate (a : Arena n) (i j : Fin n) (off : Word) (member : off∈[a.rhs,a.ap]) :
    Sources.Disjoint (a.slot a.output i) (a.slot off j) := by
  have apart := a.separated off member
  have hi := i.isLt; have hj := j.isLt
  unfold Sources.Disjoint Arena.slot
  omega

variable {n : Nat} {a : Arena n} {memory : Memory} {regs : Fin n → Registers}
  {t : Fin n → Flow.State} {words : List (Event n)} {indices : List (Fin n × IndexSources.Access)}

theorem Arena.parallel_access
    (run : Flow.Parallel.Runs a.context a.program (fun i => a.start memory (regs i)) words indices t)
    (member : Event.data thread access∈words) :
    access.space=.global ∧
    (if access.data.store then access.data.address=a.slot a.output thread
     else access.data.address=a.slot a.rhs thread ∨ access.data.address=a.slot a.ap thread) := by
  have shape := accesses (Flow.Parallel.project run thread) (address_initial rfl) (Flow.Parallel.word_member.mpr member)
  unfold AccessAt at shape
  have addr (off : Word) (member : off∈[a.rhs,a.ap,a.output]) :
      (address64 (a.context thread).arena (Kernel.Residual.index (a.context thread)) off).toNat=a.slot off thread := a.address thread off member
  simp only [addr a.rhs (by simp),addr a.ap (by simp),addr a.output (by simp)] at shape
  refine ⟨shape.1,?_⟩
  by_cases writing : access.data.store=true
  · simp only [writing,↓reduceIte] at shape ⊢; exact shape.2.2
  · simp only [writing] at shape ⊢; exact shape.2.imp And.right And.right

theorem Arena.indices_empty
    (run : Flow.Parallel.Runs a.context a.program (fun i => a.start memory (regs i)) words indices t) : indices=[] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  rintro ⟨owner,access⟩ member
  have impossible := Flow.Parallel.index_member.mpr member
  rw [no_indices (Flow.Parallel.project run owner)] at impossible
  simp at impossible

end PtxTorchLean.Poisson.PTX.FreshResidual

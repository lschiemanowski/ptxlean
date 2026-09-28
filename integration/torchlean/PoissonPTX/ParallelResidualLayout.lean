import PoissonPTX.ParallelResidualOutput

namespace PtxTorchLean.Poisson.PTX.Weak.Residual.Parallel
open Kernel Sources

/-- The geometric contract of the emitted contiguous arrays. The output is
disjoint from the inputs; input arrays may overlap because neither is written. -/
structure Arena (n : Nat) where
  base : Word
  rhs : Word
  ap : Word
  output : Word
  bytes : Nat
  small : n < 2^30
  aligned : base.toNat % 8=0
  noWrap : base.toNat+bytes ≤ 2^64
  fields : ∀ off ∈ [rhs,ap,output], off.toNat % 8=0 ∧ off.toNat+n*8 ≤ bytes
  separated : ∀ off ∈ [rhs,ap], output.toNat+n*8 ≤ off.toNat ∨ off.toNat+n*8 ≤ output.toNat

def Arena.context (a : Arena n) (i : Fin n) : Context :=
  ⟨a.base,BitVec.ofNat 32 (i.val%256),BitVec.ofNat 32 (i.val/256)⟩

def Arena.start (a : Arena n) (memory : Memory) (regs : Fin n → Registers) (i : Fin n) : Kernel.State :=
  { core := {
      pc := 0
      regs := regs i
      global := memory
      shared := fun _ => 0
      globalStart := a.base.toNat
      globalBytes := a.bytes
      sharedStart := 0
      sharedBytes := 0 }
    predicate := false
    halted := false }


theorem Arena.index (a : Arena n) (i : Fin n) :
    (Kernel.Residual.index (a.context i)).toNat = i.val := by
  have hi:=i.isLt; have hn:=a.small
  simp [Kernel.Residual.index,Arena.context,BitVec.toNat_add,BitVec.toNat_mul]
  omega

theorem Arena.live (a : Arena n) (i : Fin n) :
    Kernel.Residual.live (a.context i) (BitVec.ofNat 32 n) := by
  unfold Kernel.Residual.live
  rw [a.index i]
  have hn : n<2^32 := by have h:=a.small; omega
  change i.val < n % 2^32
  rw [Nat.mod_eq_of_lt hn]
  exact i.isLt

def Arena.inputs (a : Arena n) (memory : Memory) (regs : Fin n → Registers) : Inputs n where
  context := a.context
  start := a.start memory regs
  initial := memory
  count := BitVec.ofNat 32 n
  rhs := a.rhs
  ap := a.ap
  output := a.output
  pc := fun _ => rfl
  running := fun _ => rfl
  live := a.live
  memory := fun _ => rfl
  valid := by
    intro i off hf
    apply Kernel.Residual.field_valid _ _ _ _ (a.live i) rfl a.aligned (a.fields off hf).1
    · have hn : n<2^32 := by have h:=a.small; omega
      change off.toNat+(n%2^32)*8 ≤ a.bytes
      rw [Nat.mod_eq_of_lt hn]
      exact (a.fields off hf).2
    · exact a.noWrap

theorem Arena.addr (a : Arena n) (memory : Memory) (regs : Fin n → Registers)
    (i : Fin n) (off : Word) (hf : off∈[a.rhs,a.ap,a.output]) :
    (a.inputs memory regs).addr i off = a.base.toNat+i.val*8+off.toNat := by
  unfold Inputs.addr Arena.inputs
  rw [Kernel.Residual.setup_address,address64_exact _ _ _ ?_,a.index i]
  · rfl
  · have hb:=a.noWrap; have ho:=(a.fields off hf).2; have hi:=i.isLt
    change a.base.toNat+(Kernel.Residual.index (a.context i)).toNat*8+off.toNat<2^64
    rw [a.index i]; omega

theorem Arena.input_separation (a : Arena n) (memory : Memory) (regs : Fin n → Registers) :
    ∀ i j, Sources.Disjoint ((a.inputs memory regs).addr j a.output) ((a.inputs memory regs).addr i a.rhs) ∧
      Sources.Disjoint ((a.inputs memory regs).addr j a.output) ((a.inputs memory regs).addr i a.ap) := by
  intro i j
  rw [a.addr _ _ j a.output (by simp),a.addr _ _ i a.rhs (by simp),a.addr _ _ i a.ap (by simp)]
  have hi:=i.isLt; have hj:=j.isLt
  have hr:=a.separated a.rhs (by simp); have ha:=a.separated a.ap (by simp)
  unfold Sources.Disjoint
  omega

theorem Arena.output_ownership (a : Arena n) (memory : Memory) (regs : Fin n → Registers) :
    ∀ i j, i≠j → Sources.Disjoint ((a.inputs memory regs).addr i a.output) ((a.inputs memory regs).addr j a.output) := by
  intro i j hd
  rw [a.addr _ _ i a.output (by simp),a.addr _ _ j a.output (by simp)]
  have ne : i.val≠j.val := fun h => hd (Fin.ext h)
  unfold Sources.Disjoint
  omega

/-- The physical 256-thread indexing covers each active vector coordinate, with
no wrapping and one disjoint output word per owner. -/
theorem Arena.correspondence (a : Arena n) (memory : Memory) (regs : Fin n → Registers)
    (c : Candidate (a.inputs memory regs)) (source)
    (compatible : Compatible memory (events (a.inputs memory regs) c) source)
    (order : List (Fin n)) (complete : ∀ i, i∈order) :
    Kernel.Residual.view (publish (a.inputs memory regs) c order)
        (fun i : Fin n => a.base.toNat+i.val*8+a.output.toNat) =
      TorchLean.Tensor.subSpec
        (Kernel.Residual.view memory (fun i : Fin n => a.base.toNat+i.val*8+a.rhs.toNat))
        (Kernel.Residual.view memory (fun i : Fin n => a.base.toNat+i.val*8+a.ap.toNat)) := by
  have h:=torchlean_output (a.inputs memory regs) c source compatible
    (a.input_separation memory regs) (a.output_ownership memory regs) order complete
  change Kernel.Residual.view (publish (a.inputs memory regs) c order)
    (fun i => (a.inputs memory regs).addr i a.output) =
      TorchLean.Tensor.subSpec
        (Kernel.Residual.view memory (fun i => (a.inputs memory regs).addr i a.rhs))
        (Kernel.Residual.view memory (fun i => (a.inputs memory regs).addr i a.ap)) at h
  simpa only [a.addr memory regs _ a.output (by simp),
    a.addr memory regs _ a.rhs (by simp), a.addr memory regs _ a.ap (by simp)] using h

end PtxTorchLean.Poisson.PTX.Weak.Residual.Parallel

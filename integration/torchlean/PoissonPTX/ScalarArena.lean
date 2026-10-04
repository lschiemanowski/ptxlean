import PoissonPTX.ScalarEntry
import PoissonPTX.ScalarFrames

namespace PtxTorchLean.Poisson.PTX.Scalar

/-- Named scalar fields shared by the solver's single-thread entries. -/
inductive Field where
  | rhsSquare | trueSquare | rhsNorm | residual | rtol | atol | tolerance
  | rho | rhoNext | denominator | rr | alpha | beta
  | active | broken | useStep
  deriving DecidableEq, Repr

def Field.width : Field → Nat
  | .active | .broken | .useStep => 4
  | _ => 8

theorem Field.width_positive (f : Field) : 0<f.width := by cases f <;> decide

/-- All named scalar fields occupy distinct, aligned, bounded byte ranges.
This is a physical layout contract, with no numerical values or outcomes. -/
structure Arena where
  base : Word
  bytes : Nat
  offset : Field → Word
  baseAligned : base.toNat%8=0
  aligned : ∀ f, (offset f).toNat%f.width=0
  fit : ∀ f, (offset f).toNat+f.width≤bytes
  noWrap : base.toNat+bytes≤2^64
  apart : ∀ f g, f≠g → (offset f).toNat+f.width≤(offset g).toNat ∨ (offset g).toNat+g.width≤(offset f).toNat

def Arena.slot (a : Arena) (f : Field) : Nat := a.base.toNat+(a.offset f).toNat

def Arena.context (a : Arena) : Kernel.Context := ⟨a.base,0,0⟩

def Arena.start (a : Arena) (memory : Memory) (regs : Registers) : Flow.State :=
  ⟨{pc:=0,regs:=regs,global:=memory,shared:=fun _ => 0,globalStart:=a.base.toNat,
    globalBytes:=a.bytes,sharedStart:=0,sharedBytes:=0},fun _ => false,false⟩

theorem Arena.address (a : Arena) (f : Field) : (a.base+a.offset f).toNat=a.slot f := by
  rw [BitVec.toNat_add,Nat.mod_eq_of_lt]
  · rfl
  · have := a.fit f; have := a.noWrap; have := f.width_positive; omega

theorem Arena.valid64 (a : Arena) (f : Field) (wide : f.width=8) : Valid64 a.base.toNat a.bytes (a.slot f) := by
  have alignment := a.aligned f; have fit := a.fit f
  rw [wide] at alignment fit
  refine ⟨by unfold Arena.slot; omega,?_,by unfold Arena.slot; omega,a.noWrap⟩
  simp [Arena.slot,Nat.add_mod,a.baseAligned,alignment]

theorem Arena.valid32 (a : Arena) (f : Field) (narrow : f.width=4) : Valid32 a.base.toNat a.bytes (a.slot f) := by
  have alignment := a.aligned f; have fit := a.fit f
  rw [narrow] at alignment fit
  have base4 : a.base.toNat%4=0 := by have := a.baseAligned; omega
  refine ⟨by unfold Arena.slot; omega,?_,by unfold Arena.slot; omega,a.noWrap⟩
  simp [Arena.slot,Nat.add_mod,base4,alignment]

theorem Arena.separate (a : Arena) (f g : Field) (different : f≠g) :
    a.slot f+f.width≤a.slot g ∨ a.slot g+g.width≤a.slot f := by
  have := a.apart f g different
  unfold Arena.slot; omega

theorem Arena.word_separate (a : Arena) (f g : Field) (different : f≠g) (hf : f.width=8) (hg : g.width=8) :
    a.slot f+8≤a.slot g ∨ a.slot g+8≤a.slot f := by simpa [hf,hg] using a.separate f g different

theorem Arena.flag_word_separate (a : Arena) (f g : Field) (different : f≠g) (hf : f.width=4) (hg : g.width=8) :
    a.slot f+4≤a.slot g ∨ a.slot g+8≤a.slot f := by simpa [hf,hg] using a.separate f g different

end PtxTorchLean.Poisson.PTX.Scalar

namespace PtxTorchLean.Poisson.PTX.Scalar

/-- A thread's parameter register and allocation agree with the arena. -/
def Arena.Ready (a : Arena) (s : Flow.State) : Prop :=
  s.core.regs 0=a.base ∧ s.core.globalStart=a.base.toNat ∧ s.core.globalBytes=a.bytes

theorem Arena.setup_ready (a : Arena) (memory : Memory) (regs : Registers) :
    a.Ready (setup a.context (a.start memory regs)) := by
  simp [Arena.Ready,setup_frame.2.1,setup_frame.2.2.1,setup_frame.2.2.2.1,Arena.start,Arena.context]

variable {a : Arena} {s : Flow.State} {offset : Word} {value : Operand} {dst : Nat}

theorem Arena.state_address (ready : a.Ready s) (f : Field) : (s.core.regs 0+a.offset f).toNat=a.slot f := by
  rw [ready.1,a.address]

theorem Arena.state_valid64 (ready : a.Ready s) (f : Field) (wide : f.width=8) :
    Valid64 s.core.globalStart s.core.globalBytes (s.core.regs 0+a.offset f).toNat := by
  rw [ready.2.1,ready.2.2,a.state_address ready]
  exact a.valid64 f wide

theorem Arena.state_valid32 (ready : a.Ready s) (f : Field) (narrow : f.width=4) :
    Valid32 s.core.globalStart s.core.globalBytes (s.core.regs 0+a.offset f).toNat := by
  rw [ready.2.1,ready.2.2,a.state_address ready]
  exact a.valid32 f narrow

theorem Arena.ready_load64 (ready : a.Ready s) (dst0 : dst≠0) : a.Ready (loaded64 s dst offset) := by
  simpa only [Arena.Ready,(loaded64_frame dst0).2.1,(loaded64_frame dst0).2.2.1,
    (loaded64_frame dst0).2.2.2.1] using ready

theorem Arena.ready_store64 (ready : a.Ready s) : a.Ready (stored64 s offset value) := by
  simpa only [Arena.Ready,stored64_frame.1,stored64_frame.2.1,stored64_frame.2.2.1] using ready

end PtxTorchLean.Poisson.PTX.Scalar

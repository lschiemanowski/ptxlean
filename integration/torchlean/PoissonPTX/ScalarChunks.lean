import PoissonPTX.ScalarObservedTransfers

namespace PtxTorchLean.Poisson.PTX.Scalar

/-- Proof grouping of the existing instruction lists. Memory chunks include
the three actual address instructions and the actual transfer instruction. -/
inductive Chunk where
  | load64 (field : Field) (dst : Nat)
  | load32 (field : Field) (dst : Nat)
  | store64 (field : Field) (value : Operand)
  | store32 (field : Field) (value : Operand)
  | pure (code : List Instr)
  deriving DecidableEq, Repr

def Chunk.code (offset : Field → Word) : Chunk → List Instr
  | .load64 f dst => load64Code dst (offset f)
  | .load32 f dst => load32Code dst (offset f)
  | .store64 f value => store64Code (offset f) value
  | .store32 f value => store32Code (offset f) value
  | .pure code => code

def Chunk.valid : Chunk → Prop
  | .load64 f dst => f.width=8 ∧ dst≠0
  | .load32 f dst => f.width=4 ∧ dst≠0
  | .store64 f _ => f.width=8
  | .store32 f _ => f.width=4
  | .pure code => ∀ i∈code, Observed.noMemory i=true ∧ Observed.keepsBase i=true ∧ segment i=true

/-- An access footprint contains no loaded/stored value. -/
structure Footprint where
  pc : Nat
  store : Bool
  field : Field
  deriving DecidableEq, Repr

def Chunk.footprint (pc : Nat) : Chunk → List Footprint
  | .load64 f _ | .load32 f _ => [⟨pc+3,false,f⟩]
  | .store64 f _ | .store32 f _ => [⟨pc+3,true,f⟩]
  | .pure _ => []

def Footprint.Matches (a : Arena) (f : Footprint) (event : Sources.Access) : Prop :=
  event.pc=f.pc ∧ event.store=f.store ∧ event.space=.global ∧ event.address=a.slot f.field ∧ event.width.bytes=f.field.width

def chunksCode (offset : Field → Word) (chunks : List Chunk) : List Instr := chunks.flatMap (Chunk.code offset)

def footprints (offset : Field → Word) (pc : Nat) : List Chunk → List Footprint
  | [] => []
  | chunk::rest => chunk.footprint pc++footprints offset (pc+(chunk.code offset).length) rest

variable {chunk : Chunk}

theorem Chunk.safe (valid : chunk.valid) : ∀ i∈chunk.code offset, Observed.keepsBase i=true ∧ segment i=true := by
  cases chunk with
  | pure code => exact fun i mem => (valid i mem).2
  | _ =>
    simp_all [Chunk.valid,Chunk.code,load64Code,ScalarLoad.code,store64Code,store64Ops,load32Code,store32Code,address4Code,ops,
      Observed.keepsBase,Observed.indexedKeepsBase,Observed.dataKeepsBase,segment,Flow.segment]

theorem Chunk.accesses {a : Arena} (actual : Observed.Sequence ctx (chunk.code a.offset) s events t)
    (valid : chunk.valid) (running : s.halted=false) (ready : a.Ready s) :
    ∀ event∈events, ∃ f∈chunk.footprint s.core.pc, f.Matches a event := by
  cases chunk with
  | pure code =>
    have empty := (Observed.no_memory_sequence actual (fun i mem => (valid i mem).1)).1
    simp [empty]
  | load64 field dst =>
    obtain ⟨event,eq,pc,store,space,address,width⟩ := Observed.load64_transfer actual running ready valid.1
    intro other member
    have same : other=event := by simpa [eq] using member
    subst other
    exact ⟨⟨s.core.pc+3,false,field⟩,by simp [Chunk.footprint],pc,store,space,address,width⟩
  | load32 field dst =>
    obtain ⟨event,eq,pc,store,space,address,width⟩ := Observed.load32_transfer actual running ready valid.1
    intro other member
    have same : other=event := by simpa [eq] using member
    subst other
    exact ⟨⟨s.core.pc+3,false,field⟩,by simp [Chunk.footprint],pc,store,space,address,width⟩
  | store64 field value =>
    obtain ⟨event,eq,pc,store,space,address,width⟩ := Observed.store64_transfer actual running ready valid
    intro other member
    have same : other=event := by simpa [eq] using member
    subst other
    exact ⟨⟨s.core.pc+3,true,field⟩,by simp [Chunk.footprint],pc,store,space,address,width⟩
  | store32 field value =>
    obtain ⟨event,eq,pc,store,space,address,width⟩ := Observed.store32_transfer actual running ready valid
    intro other member
    have same : other=event := by simpa [eq] using member
    subst other
    exact ⟨⟨s.core.pc+3,true,field⟩,by simp [Chunk.footprint],pc,store,space,address,width⟩

end PtxTorchLean.Poisson.PTX.Scalar

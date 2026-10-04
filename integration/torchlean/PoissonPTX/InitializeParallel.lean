import PoissonPTX.InitializeArena
import PoissonPTX.ObservedParallelPublication

namespace PtxTorchLean.Poisson.PTX.Initialize
open Concurrent
variable {n : Nat} {a : Arena n} {memory : Memory} {regs : Fin n → Registers}
  {t : Fin n → Flow.State} {words : List (Event n)} {indices : List (Fin n × IndexSources.Access)}

def Arena.loadWord (a : Arena n) (memory : Memory) (i : Fin n) : Word :=
  if read32 memory (a.base.toNat+a.boundary.toNat+i.val*4)=0 then read64 memory (a.slot .input i) else 0

def Arena.quotient (a : Arena n) (memory : Memory) (i : Fin n) : Float :=
  decode (a.loadWord memory i)/decode
    (if read32 memory (a.base.toNat+a.boundary.toNat+i.val*4)=0 then read64 memory (a.slot .diagonal i) else PreconditionUpdate.one)

theorem Arena.separated
    (run : Flow.Parallel.Runs a.context a.program (fun i => a.start memory (regs i)) words indices t) :
    Flow.Parallel.Separate words indices := by
  constructor
  · intro writer wa written store reader ra readmem read same
    have write := a.parallel_access run written
    have load := a.parallel_access run readmem
    simp only [store,↓reduceIte] at write
    simp only [read,Bool.false_eq_true,↓reduceIte] at load
    obtain ⟨f,output,storeAddress⟩ := write.2
    obtain ⟨g,input,readAddress⟩ := load.2
    rw [storeAddress,readAddress]
    apply a.owners f g writer reader
    exact Or.inl (by rcases output with rfl|rfl|rfl|rfl|rfl <;> rcases input with rfl|rfl <;> decide)
  · intro writer wa written store global reader ra readmem
    have write := a.parallel_access run written
    simp only [store,↓reduceIte] at write
    obtain ⟨f,_,storeAddress⟩ := write.2
    rw [storeAddress,a.parallel_index run readmem]
    exact a.boundary_disjoint f writer reader

theorem Arena.publication
    (run : Flow.Parallel.Runs a.context a.program (fun i => a.start memory (regs i)) words indices t)
    (field : Field) (thread : Fin n) :
    read64 (GlobalPublication.publish memory words) (a.slot field thread)=read64 (t thread).core.global (a.slot field thread) := by
  apply Flow.Parallel.publication_word run rfl
  intro owner access member different global store
  have write := a.parallel_access run member
  simp only [store,↓reduceIte] at write
  obtain ⟨f,_,address⟩ := write.2
  rw [address]
  exact a.owners field f thread owner (Or.inr (Ne.symm different))

theorem Arena.local_correct {regs : Registers}
    (run : Flow.Runs (a.context i) a.program (a.start memory regs) final) (done : final.halted=true) :
    read64 final.core.global (a.slot .rhs i)=a.loadWord memory i ∧
    read64 final.core.global (a.slot .r i)=a.loadWord memory i ∧
    decode (read64 final.core.global (a.slot .z i))=a.quotient memory i ∧
    read64 final.core.global (a.slot .p i)=read64 final.core.global (a.slot .z i) ∧
    read64 final.core.global (a.slot .x i)=0 := by
  have result := entry_correct run rfl rfl done (a.live i) (a.local_valid memory regs i) (a.local_separate memory regs i)
  simp only [Initialize.quotient,Initialize.loadWord,PreconditionUpdate.divisor,Assembly.maskFlag,a.setup_address,a.setup_boundary] at result
  exact ⟨result.1,result.2.1,result.2.2.1,result.2.2.2.1,result.2.2.2.2.1⟩

/-- Actual publication initializes all five output arrays from admitted input bytes. -/
theorem Arena.parallel_correct
    (run : Flow.Parallel.Runs a.context a.program (fun i => a.start memory (regs i)) words indices t)
    (compatible : Visibility.Compatible (fun space => match space with | .global => memory | .shared => fun _ => 0) words source)
    (indexCompatible : IndexSources.Compatible memory words indices indexSource)
    (done : ∀ i, (t i).halted=true) (thread : Fin n) :
    read64 (GlobalPublication.publish memory words) (a.slot .rhs thread)=a.loadWord memory thread ∧
    read64 (GlobalPublication.publish memory words) (a.slot .r thread)=a.loadWord memory thread ∧
    decode (read64 (GlobalPublication.publish memory words) (a.slot .z thread))=a.quotient memory thread ∧
    read64 (GlobalPublication.publish memory words) (a.slot .p thread)=read64 (GlobalPublication.publish memory words) (a.slot .z thread) ∧
    read64 (GlobalPublication.publish memory words) (a.slot .x thread)=0 := by
  rw [a.publication run .rhs thread,a.publication run .r thread,a.publication run .z thread,a.publication run .p thread,a.publication run .x thread]
  exact a.local_correct (Flow.Parallel.replay run compatible indexCompatible (a.separated run) (fun _ => rfl) thread) (done thread)

theorem Arena.publication_outside {byte : Nat}
    (run : Flow.Parallel.Runs a.context a.program (fun i => a.start memory (regs i)) words indices t)
    (outside : ∀ f, f=Field.rhs ∨ f=Field.r ∨ f=Field.z ∨ f=Field.p ∨ f=Field.x →
      byte<a.base.toNat+(a.vector f).toNat ∨ a.base.toNat+(a.vector f).toNat+n*8≤byte) :
    GlobalPublication.publish memory words byte=memory byte := by
  apply GlobalPublication.outside
  intro owner access member global store
  have write := a.parallel_access run member
  simp only [store,↓reduceIte] at write
  obtain ⟨f,kind,address⟩ := write.2
  rw [address]
  have bounds := outside f kind
  unfold ArrayArena.slot
  have := owner.isLt; omega

end PtxTorchLean.Poisson.PTX.Initialize

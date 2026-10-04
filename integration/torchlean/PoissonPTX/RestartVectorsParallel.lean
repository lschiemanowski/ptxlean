import PoissonPTX.RestartVectorsArena
import PoissonPTX.ObservedParallelPublication

namespace PtxTorchLean.Poisson.PTX.RestartVectors
open Concurrent
variable {n : Nat} {a : Arena n} {memory : Memory} {regs : Fin n → Registers}
  {t : Fin n → Flow.State} {words : List (Event n)} {indices : List (Fin n × IndexSources.Access)}

def Arena.quotient (a : Arena n) (memory : Memory) (i : Fin n) : Float :=
  decode (read64 memory (a.slot .source i))/decode
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
    exact Or.inl (by rcases output with rfl|rfl|rfl <;> rcases input with rfl|rfl <;> decide)
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
    read64 final.core.global (a.slot .r i)=read64 memory (a.slot .source i) ∧
    decode (read64 final.core.global (a.slot .z i))=a.quotient memory i ∧
    read64 final.core.global (a.slot .p i)=read64 final.core.global (a.slot .z i) := by
  have result := entry_correct run rfl rfl done (a.live i) (a.local_valid memory regs i) (a.local_separate memory regs i)
  simp only [RestartVectors.quotient,PreconditionUpdate.divisor,Assembly.maskFlag,a.setup_address,a.setup_boundary] at result
  exact ⟨result.1,result.2.1,result.2.2.1⟩

/-- The actual parallel publication copies r bit for bit and writes one actual
rounded quotient word to both z and p. Inputs follow from admitted sources. -/
theorem Arena.parallel_correct
    (run : Flow.Parallel.Runs a.context a.program (fun i => a.start memory (regs i)) words indices t)
    (compatible : Visibility.Compatible (fun space => match space with | .global => memory | .shared => fun _ => 0) words source)
    (indexCompatible : IndexSources.Compatible memory words indices indexSource)
    (done : ∀ i, (t i).halted=true) (thread : Fin n) :
    read64 (GlobalPublication.publish memory words) (a.slot .r thread)=read64 memory (a.slot .source thread) ∧
    decode (read64 (GlobalPublication.publish memory words) (a.slot .z thread))=a.quotient memory thread ∧
    read64 (GlobalPublication.publish memory words) (a.slot .p thread)=read64 (GlobalPublication.publish memory words) (a.slot .z thread) := by
  rw [a.publication run .r thread,a.publication run .z thread,a.publication run .p thread]
  exact a.local_correct (Flow.Parallel.replay run compatible indexCompatible (a.separated run) (fun _ => rfl) thread) (done thread)

theorem Arena.publication_outside {byte : Nat}
    (run : Flow.Parallel.Runs a.context a.program (fun i => a.start memory (regs i)) words indices t)
    (outside : ∀ f, f=Field.r ∨ f=Field.z ∨ f=Field.p →
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

end PtxTorchLean.Poisson.PTX.RestartVectors

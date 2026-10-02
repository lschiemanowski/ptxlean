import PoissonPTX.AssemblyParallelStores

namespace PtxTorchLean.Poisson.PTX.Assembly

/-- Two whole allocated fields do not overlap. Either order is allowed; the
emitted cell-value array lies after some of the assembly output arrays. -/
def Arena.FieldApart (a : Arena n) (field : Word) (bytes : Nat) : Prop :=
  a.output.toNat+n*8≤field.toNat ∨ field.toNat+bytes≤a.output.toNat

structure Arena.InputSeparation (a : Arena n) : Prop where
  offsets : a.FieldApart a.offsets ((n+1)*4)
  entries : a.FieldApart a.entries (a.entryCount*4)
  element : a.FieldApart a.element (a.elementCount*8)
  boundary : a.FieldApart a.boundary (n*4)

variable {n : Nat} {a : Arena n} {memory : Memory} {regs : Fin n → Registers}
  {t : Fin n → Flow.State} {words : List (Concurrent.Event n)} {indices : List (Fin n × IndexSources.Access)}

/-- Once a four-byte read is located inside a separated input field, actual
assembly store ownership forces its source bytes to initialization. -/
theorem Arena.index_initial {read : IndexSources.Access} {thread : Fin n} {field : Word} {k count : Nat}
    (run : Flow.Parallel.Runs a.context
      (entryCode (BitVec.ofNat 32 n) a.offsets a.entries a.element mask a.boundary a.output)
      (fun i => a.start memory (regs i)) words indices t)
    (compatible : IndexSources.Compatible memory words indices indexSource)
    (observed : (thread,read)∈indices)
    (located : read.address=a.base.toNat+field.toNat+k*4) (inside : k<count)
    (apart : a.FieldApart field (count*4)) : read.value=read32 memory read.address := by
  obtain ⟨r,atIndex⟩ := List.mem_iff_getElem?.mp observed
  apply IndexSources.read_only_value compatible atIndex
  apply IndexSources.readonly_of_disjoint
  intro w writer wa fetched store global
  have address := (a.parallel_store memory regs run (List.mem_of_getElem? fetched) store).2
  rw [address,located]
  have owner := writer.isLt
  unfold Arena.FieldApart at apart
  omega

/-- The same argument applies to the eight bytes of an actual floating-point
read. It does not assume atomicity or equality with a desired tensor entry. -/
theorem Arena.word_initial {read : Concurrent.Access} {thread : Fin n} {field : Word} {k count : Nat}
    (run : Flow.Parallel.Runs a.context
      (entryCode (BitVec.ofNat 32 n) a.offsets a.entries a.element mask a.boundary a.output)
      (fun i => a.start memory (regs i)) words indices t)
    (compatible : Concurrent.Visibility.Compatible initial words wordSource)
    (globalMemory : initial .global=memory)
    (observed : Concurrent.Event.data thread read∈words) (load : read.data.store=false) (global : read.space=.global)
    (located : read.data.address=a.base.toNat+field.toNat+k*8) (inside : k<count)
    (apart : a.FieldApart field (count*8)) : read.data.value=read64 memory read.data.address := by
  obtain ⟨r,atIndex⟩ := List.mem_iff_getElem?.mp observed
  have result : read.data.value=read64 (initial read.space) read.data.address := by
    apply Concurrent.Visibility.read_only_value compatible atIndex load
    intro w writer wa fetched store space j byteIndex
    have address := (a.parallel_store memory regs run (List.mem_of_getElem? fetched) store).2
    have owner := writer.isLt
    have hj := j.isLt; have hk := byteIndex.isLt
    rw [address,located]
    unfold Arena.FieldApart at apart
    omega
  simpa only [global,globalMemory] using result

end PtxTorchLean.Poisson.PTX.Assembly

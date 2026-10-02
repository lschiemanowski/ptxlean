import PoissonPTX.AssemblyRecordedWitness
import PoissonPTX.AssemblyParallelCorrespondence
import PoissonPTX.ObservedParallelExists

namespace PtxTorchLean.Poisson.PTX.Assembly

/-- Every valid physical assembly input admits a returning joint execution.
The witness uses actual scalar instruction executions and initialization
sources, not assumed outputs or a bounded interpreter search. -/
theorem Arena.parallel_exists (a : Arena n) (memory : Memory) (regs : Fin n → Registers)
    (contents : a.Contents memory) (mask : Bool) :
    ∃ words indices final,
      Flow.Parallel.Runs a.context
        (entryCode (BitVec.ofNat 32 n) a.offsets a.entries a.element mask a.boundary a.output)
        (fun i => a.start memory (regs i)) words indices final ∧
      (∀ i, (final i).halted=true) ∧
      Concurrent.Visibility.Compatible (fun space => match space with | .global => memory | .shared => fun _ => 0)
        words (fun _ _ => .initial) ∧
      IndexSources.Compatible memory words indices (fun _ _ => .initial) := by
  classical
  let c := Snapshot.witness a memory contents regs mask
  have localRecorded := fun i => recorded_witness (c.run i) (show ObservedAddress.BeforeStore memory mask (a.start memory (regs i)) from by intro _; rfl)
  choose localWords localIndices observed wordValues indexValues using localRecorded
  obtain ⟨words,indices,actual,wordMembers,indexMembers⟩ := Flow.Parallel.all_threads localWords localIndices observed
  refine ⟨words,indices,c.final,actual,c.done,?_,?_⟩
  · intro r reader read located load k
    have value := wordValues reader read (wordMembers reader read (List.mem_of_getElem? located)) load
    change byte read.data.value k.val=(match read.space with | .global => memory | .shared => fun _ => 0) (read.data.address+k.val)
    rw [value.1,value.2,Sources.byte_read64]
  · intro r reader read located k
    have value := indexValues reader read (indexMembers reader read (List.mem_of_getElem? located))
    change IndexSources.byte32 read.value k.val=memory (read.address+k.val)
    rw [value,IndexSources.byte_read32]

/-- The general admitted witness satisfies the same actual-publication
correspondence theorem used for arbitrary completed interleavings. -/
theorem Arena.parallel_exists_correct (a : Arena n) (memory : Memory) (regs : Fin n → Registers)
    (contents : a.Contents memory) (separated : a.InputSeparation) (mask : Bool) :
    ∃ words indices final,
      Flow.Parallel.Runs a.context
        (entryCode (BitVec.ofNat 32 n) a.offsets a.entries a.element mask a.boundary a.output)
        (fun i => a.start memory (regs i)) words indices final ∧
      (∀ i, (final i).halted=true) ∧
      Concurrent.Visibility.Compatible (fun space => match space with | .global => memory | .shared => fun _ => 0)
        words (fun _ _ => .initial) ∧
      IndexSources.Compatible memory words indices (fun _ _ => .initial) ∧
      ∀ i, decode (read64 (Concurrent.GlobalPublication.publish memory words) (Snapshot.address a i))=a.value memory i mask := by
  obtain ⟨words,indices,final,run,done,compatible,indexCompatible⟩ := a.parallel_exists memory regs contents mask
  exact ⟨words,indices,final,run,done,compatible,indexCompatible,
    a.parallel_value run compatible indexCompatible contents separated done⟩

end PtxTorchLean.Poisson.PTX.Assembly

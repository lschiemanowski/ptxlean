import PoissonPTX.GlobalThreadSources
import PoissonPTX.InitializeParallel
import PoissonPTX.InitializeRecorded
import PoissonPTX.ObservedParallelExists

namespace PtxTorchLean.Poisson.PTX.Initialize
open Concurrent

theorem Arena.local_exists (a : Arena n) (memory : Memory) (regs : Registers) (i : Fin n) :
    ∃ t, Flow.Runs (a.context i) a.program (a.start memory regs) t ∧ t.halted=true :=
  entry_exists _ rfl rfl (a.live i) (a.local_valid memory regs i)

/-- Construct a complete active-coordinate execution and its actual source
assignment, then obtain its numerical publication from the universal theorem.
This is finite schedule existence, not fairness or whole-PTX admission. -/
theorem Arena.parallel_exists (a : Arena n) (memory : Memory) (regs : Fin n → Registers) :
    ∃ words indices final,
      Flow.Parallel.Runs a.context a.program (fun i => a.start memory (regs i)) words indices final ∧
      (∀ i, (final i).halted=true) ∧
      Visibility.Compatible (fun space => match space with | .global => memory | .shared => fun _ => 0)
        words (fun _ _ => .initial) ∧
      IndexSources.Compatible memory words indices (fun _ _ => .initial) ∧
      Visibility.GlobalThreadSources words (fun _ _ => .initial) ∧
      ∀ i,
        read64 (GlobalPublication.publish memory words) (a.slot .rhs i)=a.loadWord memory i ∧
        read64 (GlobalPublication.publish memory words) (a.slot .r i)=a.loadWord memory i ∧
        decode (read64 (GlobalPublication.publish memory words) (a.slot .z i))=a.quotient memory i ∧
        read64 (GlobalPublication.publish memory words) (a.slot .p i)=read64 (GlobalPublication.publish memory words) (a.slot .z i) ∧
        read64 (GlobalPublication.publish memory words) (a.slot .x i)=0 := by
  classical
  choose final runs done using fun i => a.local_exists memory (regs i) i
  have recorded := fun i => a.recorded_witness (runs i) (address_initial rfl) (a.inputs_initial memory (regs i) i)
  choose localWords localIndices observed wordValues indexValues using recorded
  obtain ⟨words,indices,actual,wordMembers,indexMembers⟩ := Flow.Parallel.all_threads localWords localIndices observed
  have compatible : Visibility.Compatible (fun space => match space with | .global => memory | .shared => fun _ => 0)
      words (fun _ _ => .initial) := by
    intro r reader read located load k
    have value := wordValues reader read (wordMembers reader read (List.mem_of_getElem? located)) load
    change byte read.data.value k.val=(match read.space with | .global => memory | .shared => fun _ => 0) (read.data.address+k.val)
    rw [value.1,value.2,Sources.byte_read64]
  have indexCompatible : IndexSources.Compatible memory words indices (fun _ _ => .initial) := by
    intro r reader read located k
    have value := indexValues reader read (indexMembers reader read (List.mem_of_getElem? located))
    change IndexSources.byte32 read.value k.val=memory (read.address+k.val)
    rw [value,IndexSources.byte_read32]
  have admitted : Visibility.GlobalThreadSources words (fun _ _ => .initial) := Visibility.initial_thread_sources
  exact ⟨words,indices,final,actual,done,compatible,indexCompatible,admitted,
    a.parallel_correct actual compatible indexCompatible done⟩

end PtxTorchLean.Poisson.PTX.Initialize

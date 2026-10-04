import PoissonPTX.DotCompleteCandidate
import PoissonPTX.DotWitnessProducers

namespace PtxTorchLean.Poisson.PTX.Concurrent.Dot.Witness
open Reduction.Control.Witness256 Visibility.Repeated

/-- Admit the same constructed history: input loads read initial global bytes,
while tree and epilogue loads name actual shared stores preceding real barriers.
This is the existing necessary source-admission fragment, not full PTX memory
admission or a hardware-conformance assertion. -/
theorem admitted {cfg : Config 256} {ctx : Fin 256 → Kernel.Context}
    (run : NativeFlow.Runs cfg ctx (program count left right output scratch) start events indices final)
    (reset : start.core.barrier=Ptx.Barrier.reset generation)
    (entry : ∀ thread, (start.core.lanes thread).pc=0)
    (laneMap : ∀ thread, (ctx thread).lane.toNat=thread.val)
    (noWrap : scratch.toNat+2048≤2^64)
    (expected : ∀ e∈events, CandidateEvent (initial .global) input e) :
    ∃ source, Visibility.Compatible initial events source ∧ OrderedSources events source := by
  have stored : ∀ (w : Nat) (owner : Fin 256) (wa : Access), events[w]?=some (.data owner wa) →
      ∀ phase : Fin 9, wa.data.pc=storeSite phase → wa.data.value=words input phase.val owner.val := by
    intro w owner wa found phase position
    have props := Numeric.store_properties run found phase position
    rcases expected _ (List.mem_of_getElem? found) with global | tree | tail
    · have read := global.1
      rw [props.1] at read; contradiction
    · exact tree.2.2.2.1 phase position
    · rcases tail.2.2 with shared | global
      · have read := shared.2.1
        rw [props.1] at read; contradiction
      · have impossible := global.1.symm.trans props.2
        cases impossible
  apply construct_global_shared events
  · intro r reader ra found read space
    rcases expected _ (List.mem_of_getElem? found) with global | tree | tail
    · exact global.2.2
    · have impossible := tree.1.symm.trans space; cases impossible
    · rcases tail.2.2 with shared | global
      · have impossible := shared.1.symm.trans space; cases impossible
      · have impossible := read.symm.trans global.2.1; cases impossible
  · intro r reader ra found read space
    rcases expected _ (List.mem_of_getElem? found) with global | tree | tail
    · have impossible := global.2.1.symm.trans space; cases impossible
    · obtain ⟨phase,right,position⟩ := tree.2.2.1 read
      exact tree_producer run reset entry laneMap noWrap stored found phase right position (tree.2.2.2.2 phase right position)
    · rcases tail.2.2 with shared | global
      · exact final_producer run reset entry laneMap noWrap stored found shared.2.2 tail.2.1
      · have impossible := global.1.symm.trans space; cases impossible

end PtxTorchLean.Poisson.PTX.Concurrent.Dot.Witness

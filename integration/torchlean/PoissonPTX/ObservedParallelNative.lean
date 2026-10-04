import PoissonPTX.ObservedParallel
import PoissonPTX.NativeFlowAccessOrder
import PoissonPTX.ControlFlowSequence

namespace PtxTorchLean.Poisson.PTX.Flow.Parallel
open Concurrent

variable {n : Nat} {ctx : Fin n → Kernel.Context} {program : List Flow.Instr}
  {s t : Fin n → Flow.State} {words : List (Concurrent.Event n)}
  {indices : List (Fin n × IndexSources.Access)}
  {r w : Nat} {owner : Fin n} {a b : Concurrent.Access}

def native (s : Fin n → Flow.State) : NativeFlow.State n :=
  ⟨⟨fun t => (s t).core,Ptx.Barrier.reset 0,none⟩,fun t => (s t).predicates,fun t => (s t).halted⟩

theorem native_update (s : Fin n → Flow.State) (thread : Fin n) (next : Flow.State) :
    NativeFlow.update (native s) thread next=native (Function.update s thread next) := by
  simp only [native,NativeFlow.update,setLane]
  congr 2
  all_goals funext t; by_cases same : t=thread <;> simp [Function.update,same]

/-- A barrier-free parallel history embeds unchanged in the native machine.
The unused barrier configuration does not identify hardware thread blocks:
only ordinary instructions execute, with original contexts and event records. -/
theorem native_run (cfg : Config n) (run : Runs ctx program s words indices t) :
    NativeFlow.Runs cfg ctx (program.map NativeFlow.Instr.flow) (native s) words indices (native t) := by
  induction run with
  | nil => exact .nil
  | @cons selected s middle access index words indices t step rest ih =>
    obtain ⟨running,i,fetch,effect⟩ := step
    have one : NativeFlow.Step cfg ctx (program.map NativeFlow.Instr.flow) selected (native s)
        ⟨NativeFlow.update (native s) selected middle,access.toList.map (Event.data selected),index.toList.map (selected,·)⟩ := by
      apply NativeFlow.Step.flow (instruction:=i) running rfl
      · simp only [native,List.getElem?_map,fetch,Option.map_some]
      · exact effect
    rw [native_update] at one
    exact .cons one ih

theorem linear_forward (linear : ∀ i∈program, Flow.linear i=true) :
    NativeFlow.ForwardFrom (program.map NativeFlow.Instr.flow) 0 := by
  intro pc i fetch
  rw [List.getElem?_map] at fetch
  obtain ⟨op,found,same⟩ := Option.map_eq_some_iff.mp fetch
  have plain := linear op (List.mem_of_getElem? found)
  cases same
  cases i <;> simp_all [Flow.linear,NativeFlow.targets]

/-- Actual same-thread instruction order entails occurrence order in the joint
history. No order between different threads is inferred. -/
theorem before_of_pc (run : Runs ctx program s words indices t)
    (linear : ∀ i∈program, Flow.linear i=true)
    (first : words[r]?=some (.data owner a)) (second : words[w]?=some (.data owner b))
    (pc : a.data.pc<b.data.pc) : r<w := by
  let cfg : Config n := ⟨0,lt_of_le_of_lt (Nat.zero_le owner.val) owner.isLt⟩
  exact Visibility.Repeated.before_lt (NativeFlow.before_of_pc (native_run cfg run) (linear_forward linear)
    first second (Nat.zero_le _) pc)

end PtxTorchLean.Poisson.PTX.Flow.Parallel

import PtxBinary32.UnaryPointwiseReads
import PtxBinary32.ParallelUnaryAdmission

/-! Candidate execution and memory admission are distinct: a locally executable
incorrect load must be rejected by the graph. Two lanes can both load before
either writes; the adapter does not impose whole-lane serial execution. -/
namespace Ptx.Scalar.UnaryPointwise.Checks
open ParallelUnary

private def seed : Scalar.State := ⟨0,fun _=>0,fun _=>0,fun _=>false,[]⟩
private def before : List Word := [0x3f800000,0x3f800000,0x40000000]
private def start : ParallelUnary.State 2 := initial 2 before (fun _=>seed)
private def loaded (s : ParallelUnary.State 2) (t : Fin 2) (v : Word) :=
  ParallelUnary.install s t (SoftmaxMemory.write (ParallelUnary.input s t) 0 v) false
private def loadEvent (s : ParallelUnary.State 2) (t : Fin 2) (v : Word) : ParallelUnary.Event 2 :=
  .scalar t (Scalar.occurrence (ParallelUnary.input s t) (.plain (.load 0 (.reg 0))) true
    (some ⟨.load,pointer t.val,v⟩))

private theorem first_load (t : Fin 2) (v : Word) :
    ParallelUnary.Step target (program .normalize) (some v) t start (loaded start t v) (loadEvent start t v) := by
  refine ⟨by norm_num [ParallelUnary.Supported,target],rfl,ownLoad,by rfl,?_⟩
  apply ParallelUnary.Exec.scalarNext
  have index := SoftmaxMemory.address_index before t.val ⟨by simp [before]; omega,by omega⟩
  simp [Scalar.eval,Scalar.Instr.plain,Scalar.Guard.eval,Scalar.Operand64.eval,
    ownLoad,start,initial,ParallelUnary.input,loaded,loadEvent,ParallelUnary.install,
    SoftmaxMemory.write,pointer,index]

/-- Arbitrary candidate values are locally permitted; admission must filter them. -/
theorem wrong_load_executes :
    ParallelUnary.Runs target (program .normalize) start [loadEvent start 0 0] (loaded start 0 0) :=
  .cons (first_load 0 0) .nil

/-- Loading zero from initialized positive one has no admitted graph. -/
theorem wrong_load_rejected :
    ¬∃source co, ParallelUnary.Memory.Admitted (program .normalize) before [loadEvent start 0 0] source co := by
  rintro ⟨source,co,admitted⟩
  have forced := reads_initial wrong_load_executes (by decide) (by norm_num) source co admitted
    (loadEvent start 0 0) ⟨.load,pointer 0,0⟩ (by simp) rfl rfl
  norm_num [loadEvent,pointer,SoftmaxMemory.address,before] at forced

/-- A genuine interleaving: lane one loads, then lane zero loads, before stores. -/
theorem interleaved_loads :
    ∃middle final events,
      ParallelUnary.Step target (program .normalize) (some 0x3f800000) 1 start middle (loadEvent start 1 0x3f800000) ∧
      ParallelUnary.Step target (program .normalize) (some 0x3f800000) 0 middle final (loadEvent middle 0 0x3f800000) ∧
      ParallelUnary.Runs target (program .normalize) start events final ∧
      (final.lanes 0).scalar.pc=1 ∧ (final.lanes 1).scalar.pc=1 ∧
      ∃source co, ParallelUnary.Memory.Admitted (program .normalize) before events source co := by
  let middle := loaded start 1 0x3f800000
  let final := loaded middle 0 0x3f800000
  let events := [loadEvent start 1 0x3f800000,loadEvent middle 0 0x3f800000]
  have second : ParallelUnary.Step target (program .normalize) (some 0x3f800000) 0 middle final (loadEvent middle 0 0x3f800000) := by
    refine ⟨by norm_num [ParallelUnary.Supported,target],?_,ownLoad,?_,?_⟩
    · rfl
    · rfl
    · apply ParallelUnary.Exec.scalarNext
      norm_num [Scalar.eval,Scalar.Instr.plain,Scalar.Guard.eval,Scalar.Operand64.eval,ownLoad,
        middle,final,loaded,loadEvent,start,initial,ParallelUnary.input,ParallelUnary.install,
        SoftmaxMemory.write,pointer,SoftmaxMemory.address,Scalar.addressIndex,before]
  have reads : ParallelUnary.Memory.Chronology.InitialReads before events := by
    intro t occ effect member memory kind
    simp only [events,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with eq | eq
    all_goals
      simp only [loadEvent,ParallelUnary.Event.scalar.injEq] at eq
      obtain ⟨rfl,rfl⟩ := eq
      simp only [Scalar.occurrence] at memory
      cases Option.some.inj memory
      norm_num [pointer,SoftmaxMemory.address,before]
  have future : ParallelUnary.Memory.Chronology.FutureStores events := by
    intro p q e f a b hp hq ha hb _ store _
    have member := List.mem_of_getElem? hq
    simp only [events,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl
    all_goals
      simp only [loadEvent,ParallelUnary.Event.memory,Scalar.occurrence] at hb
      cases Option.some.inj hb
      contradiction
  obtain ⟨source,co,valid,_⟩ := ParallelUnary.Memory.Chronology.admitted_of_initial_reads
    (program:=program .normalize) reads future
  exact ⟨middle,final,events,first_load 1 0x3f800000,second,
    .cons (first_load 1 0x3f800000) (.cons second .nil),by rfl,by rfl,source,co,valid⟩

end Ptx.Scalar.UnaryPointwise.Checks

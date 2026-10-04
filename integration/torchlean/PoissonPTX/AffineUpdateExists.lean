import PoissonPTX.AffineUpdateParallel
import PoissonPTX.AffineUpdateRecorded
import PoissonPTX.ObservedParallelExists

namespace PtxTorchLean.Poisson.PTX.AffineUpdate
open Concurrent

theorem Arena.local_exists (a : Arena n) (memory : Memory) (regs : Registers) (i : Fin n) :
    ∃ t, Flow.Runs (a.context i) a.program (a.start memory regs) t ∧ t.halted=true := by
  apply entry_exists _ rfl rfl (a.live i)
  · change Valid64 a.base.toNat a.bytes (a.base+a.coefficient).toNat
    rw [a.scalar_address]
    refine ⟨by omega,?_,?_,a.noWrap⟩
    · simp [Nat.add_mod,a.aligned,a.coefficientAligned]
    · have := a.coefficientFit; omega
  · exact a.vector_valid memory regs i a.direction a.directionFit a.directionAligned
  · exact a.vector_valid memory regs i a.shift a.shiftFit a.shiftAligned
  · exact a.vector_valid memory regs i a.direction a.directionFit a.directionAligned

/-- A finite admitted execution exists for every physical layout and arbitrary
initial binary64 words. No floating-point finiteness or desired result is assumed.
This gives one terminating schedule, not GPU scheduler fairness. -/
theorem Arena.parallel_exists (a : Arena n) (memory : Memory) (regs : Fin n → Registers) :
    ∃ words indices final,
      Flow.Parallel.Runs a.context a.program (fun i => a.start memory (regs i)) words indices final ∧
      (∀ i, (final i).halted=true) ∧
      Visibility.Compatible (fun space => match space with | .global => memory | .shared => fun _ => 0)
        words (fun _ _ => .initial) ∧
      Visibility.GlobalThreadSources words (fun _ _ => .initial) ∧
      indices=[] ∧
      ∀ i, decode (read64 (GlobalPublication.publish memory words) (a.slot i))=a.value memory i := by
  classical
  choose final runs done using fun i => a.local_exists memory (regs i) i
  have recorded := fun i => recorded_witness (runs i) (address_initial rfl) (show BeforeStore memory (a.start memory (regs i)) from by intro _; rfl)
  choose localWords localIndices observed wordValues empty using recorded
  obtain ⟨words,indices,actual,wordMembers,indexMembers⟩ := Flow.Parallel.all_threads localWords localIndices observed
  have compatible : Visibility.Compatible (fun space => match space with | .global => memory | .shared => fun _ => 0)
      words (fun _ _ => .initial) := by
    intro r reader read located load k
    have value := wordValues reader read (wordMembers reader read (List.mem_of_getElem? located)) load
    change byte read.data.value k.val=(match read.space with | .global => memory | .shared => fun _ => 0) (read.data.address+k.val)
    rw [value.1,value.2,Sources.byte_read64]
  have admitted : Visibility.GlobalThreadSources words (fun _ _ => .initial) := Visibility.initial_thread_sources
  refine ⟨words,indices,final,actual,done,compatible,admitted,?_,a.parallel_value actual compatible admitted done⟩
  apply List.eq_nil_iff_forall_not_mem.mpr
  rintro ⟨owner,access⟩ member
  have bad := indexMembers owner access member
  simp [empty owner] at bad

end PtxTorchLean.Poisson.PTX.AffineUpdate

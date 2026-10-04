import PoissonPTX.AffineUpdateAccess
import PoissonPTX.AffineUpdateArena
import PoissonPTX.ObservedParallelNative
import PoissonPTX.GlobalThreadSources

namespace PtxTorchLean.Poisson.PTX.AffineUpdate
open Concurrent
variable {n : Nat} {a : Arena n} {memory : Memory} {regs : Fin n → Registers}
  {r : Nat} {reader : Fin n} {ra : Access}
  {t : Fin n → Flow.State} {words : List (Event n)} {indices : List (Fin n × IndexSources.Access)}

theorem Arena.parallel_access
    (run : Flow.Parallel.Runs a.context a.program (fun i => a.start memory (regs i)) words indices t)
    (member : Event.data thread access∈words) :
    access.space=.global ∧
    (if access.data.store then access.data.pc=23 ∧ access.data.address=a.slot thread
     else (access.data.pc=9 ∧ access.data.address=a.base.toNat+a.coefficient.toNat) ∨
       (access.data.pc=13 ∧ access.data.address=a.slot thread) ∨
       (access.data.pc=17 ∧ access.data.address=a.base.toNat+a.shift.toNat+thread.val*8)) := by
  have shape := accesses (Flow.Parallel.project run thread) (address_initial rfl) (Flow.Parallel.word_member.mpr member)
  unfold AccessAt at shape
  change access.space=.global ∧
    (if access.data.store then access.data.pc=23 ∧ access.data.address=(address64 a.base (Kernel.Residual.index (a.context thread)) a.direction).toNat
     else (access.data.pc=9 ∧ access.data.address=(a.base+a.coefficient).toNat) ∨
       (access.data.pc=13 ∧ access.data.address=(address64 a.base (Kernel.Residual.index (a.context thread)) a.direction).toNat) ∨
       (access.data.pc=17 ∧ access.data.address=(address64 a.base (Kernel.Residual.index (a.context thread)) a.shift).toNat)) at shape
  change access.space=.global ∧ _
  simpa only [a.scalar_address,a.vector_address thread a.direction a.directionFit,
    a.vector_address thread a.shift a.shiftFit,Arena.slot] using shape

/-- Every actual load uses initial bytes. Read-only fields have no writers;
an old direction word can only overlap its own thread's later store. -/
theorem Arena.read_value
    (run : Flow.Parallel.Runs a.context a.program (fun i => a.start memory (regs i)) words indices t)
    (compatible : Visibility.Compatible (fun space => match space with | .global => memory | .shared => fun _ => 0) words source)
    (admitted : Visibility.GlobalThreadSources words source)
    (observed : words[r]?=some (.data reader ra)) (read : ra.data.store=false) :
    ra.data.value=read64 memory ra.data.address := by
  have shape := a.parallel_access run (List.mem_of_getElem? observed)
  have global := shape.1
  simp only [read,Bool.false_eq_true,↓reduceIte] at shape
  rcases shape.2 with coefficient | direction | shift
  · have readonly : Visibility.ReadOnly words ra.space ra.data.address := by
      intro w owner wa fetched store same j k overlap
      have write := a.parallel_access run (List.mem_of_getElem? fetched)
      simp only [store,↓reduceIte] at write
      have apart := a.coefficientApart
      have ownerBound := owner.isLt; have hj := j.isLt; have hk := k.isLt
      rw [write.2.2,coefficient.2] at overlap
      unfold Arena.slot at overlap
      omega
    simpa only [global] using Visibility.read_only_value compatible observed read readonly
  · have chosen := Visibility.before_own_writes_initial compatible admitted observed read global
    apply chosen (fun w owner wa fetched store wg j k overlap => ?_) |>.2
    have write := a.parallel_access run (List.mem_of_getElem? fetched)
    simp only [store,↓reduceIte] at write
    have hj := j.isLt; have hk := k.isLt
    have ownerEq : owner=reader := by
      apply Fin.ext
      rw [write.2.2,direction.2] at overlap
      unfold Arena.slot at overlap
      omega
    subst owner
    refine ⟨rfl,?_,write.2.2.trans direction.2.symm⟩
    apply Flow.Parallel.before_of_pc run entry_linear observed fetched
    omega
  · have readonly : Visibility.ReadOnly words ra.space ra.data.address := by
      intro w owner wa fetched store same j k overlap
      have write := a.parallel_access run (List.mem_of_getElem? fetched)
      simp only [store,↓reduceIte] at write
      have apart := a.shiftApart
      have ownerBound := owner.isLt; have readerBound := reader.isLt; have hj := j.isLt; have hk := k.isLt
      rw [write.2.2,shift.2] at overlap
      unfold Arena.slot at overlap
      omega
    simpa only [global] using Visibility.read_only_value compatible observed read readonly

end PtxTorchLean.Poisson.PTX.AffineUpdate

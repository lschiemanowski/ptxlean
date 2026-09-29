import PoissonPTX.CellConsumerValues

namespace PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer
open CellMiddle Symbolic Correspondence

theorem expected_tensor (bases : Space → Word) (memory : Space → Nat → Word) (i j : Fin width) :
    (expected width (i.val*width+j.val)).eval bases memory=
      Spec.get2 (plus
        (Spec.matMulSpec (matrix (Numeric.grid width bases memory .shared (5*width*width*8)))
          (matrix (Numeric.grid width bases memory .global (width*width*8+32))))
        (Spec.matMulSpec (matrix (Numeric.grid width bases memory .shared (6*width*width*8)))
          (matrix (Numeric.grid width bases memory .global 0)))) i j := by
  obtain ⟨row,col⟩ := Numeric.row_col i j
  change _=entries _ i j
  simp only [entries_summed,entries_product,entries_matrix,expected,row,col,Number.eval,FP.apply,
    Numeric.sum_eval,Numeric.entry_eval]
  rfl

/-- Whole-history source constraints justify the real final loads. The resulting
register equals the TorchLean local cell calculation, without a snapshot premise. -/
theorem completed_arithmetic (launch : Numeric.Launch width bases start) (lo : 2≤width) (hi : width≤5)
    (middle : Runs cfg (Checks.program width) start before ready)
    (done : ∀ t, (ready.lanes t).pc=(Checks.program width).length)
    (rest : Runs cfg (program width) ready after final)
    (compatible : Visibility.Compatible initial (before++after) source)
    (performed : Visibility.Performed (before++after) source)
    (thread : Fin 32) (i j : Fin width) (lane : thread.val=i.val*width+j.val)
    (finished : (final.lanes thread).pc=(program width).length) :
    decode ((final.lanes thread).regs 11)=Spec.get2 (localAction
      (Numeric.initialTensor width bases initial .global 0)
      (Numeric.initialTensor width bases initial .global (width*width*8+32))
      (Numeric.initialTensor width bases initial .global (2*(width*width*8+32)))
      (Numeric.initialTensor width bases initial .shared 0)) i j := by
  have readonly := tail_readonly lo hi rest done
  have pc := Extension.compatible_prefix compatible readonly
  have pp := Extension.performed_prefix performed
  have h := register_value launch lo hi middle done rest compatible performed thread
    (by rw [lane]; exact row_major_bound i j) finished
  rw [lane,expected_tensor] at h
  have m5 := Numeric.completed_middle launch lo hi middle done pc pp ⟨5,by decide⟩ (by decide)
  have m6 := Numeric.completed_middle launch lo hi middle done pc pp ⟨6,by decide⟩ (by decide)
  change _=entries _ i j at h ⊢
  simp only [entries_summed,entries_product,entries_matrix] at h
  rw [m5,m6,Numeric.global_grid,Numeric.global_grid] at h
  simpa [Numeric.target,localAction,entries_summed,entries_product] using h

/-- The existing fetched index/store/return proof starts from the actual
concurrent result state. It is still a separate model for the final tail. -/
theorem stored_local (launch : Numeric.Launch width bases start) (lo : 2≤width) (hi : width≤5)
    (middle : Runs cfg (Checks.program width) start before ready)
    (done : ∀ t, (ready.lanes t).pc=(Checks.program width).length)
    (rest : Runs cfg (program width) ready after final)
    (compatible : Visibility.Compatible initial (before++after) source)
    (performed : Visibility.Performed (before++after) source)
    (thread : Fin 32) (i j : Fin width) (lane : thread.val=i.val*width+j.val)
    (finished : (final.lanes thread).pc=(program width).length)
    (valid : Valid64 (final.lanes thread).globalStart (final.lanes thread).globalBytes
      (CellFinal.location (final.lanes thread) width output).toNat)
    (precode : List Kernel.Instr) (pc : (final.lanes thread).pc=precode.length)
    (tailRun : Kernel.Run ctx (precode++CellFinal.tail width output)
      ⟨final.lanes thread,false,false⟩ stored) :
    decode (read64 stored.core.global (CellFinal.location (final.lanes thread) width output).toNat)=
      Spec.get2 (localAction
        (Numeric.initialTensor width bases initial .global 0)
        (Numeric.initialTensor width bases initial .global (width*width*8+32))
        (Numeric.initialTensor width bases initial .global (2*(width*width*8+32)))
        (Numeric.initialTensor width bases initial .shared 0)) i j := by
  have h := CellFinal.tail_correct rfl valid (Kernel.run_exec tailRun precode _ rfl pc)
  exact h.1.trans (completed_arithmetic launch lo hi middle done rest compatible performed thread i j lane finished)

theorem tail_completion (s : PTX.State) (valid : Valid64 s.globalStart s.globalBytes (CellFinal.location s width output).toNat)
    (precode : List Kernel.Instr) (pc : s.pc=precode.length) :
    ∃ stored, Kernel.Run ctx (precode++CellFinal.tail width output) ⟨s,false,false⟩ stored := by
  obtain ⟨stored,run⟩ := CellFinal.tail_exists (ctx:=ctx) (width:=width) (output:=output) ⟨s,false,false⟩ rfl valid
  exact ⟨stored,Kernel.exec_fetched run precode pc⟩

end PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer

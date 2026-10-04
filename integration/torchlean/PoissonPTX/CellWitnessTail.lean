import PoissonPTX.CellWitnessTailLocal

namespace PtxTorchLean.Poisson.PTX.CellFinal
open Kernel

/-- The concrete store tail terminates after its six fetched instructions. -/
theorem tail_exists_complete (s : Kernel.State) (running : s.halted=false)
    (valid : Valid64 s.core.globalStart s.core.globalBytes (location s.core width output).toNat) :
    ∃ final, Exec ctx (tail width output) s final ∧ final.halted=true ∧ final.core.pc=s.core.pc+6 := by
  let next := simple ctx (.mad32 13 15 (BitVec.ofNat 32 (width*width)) 14) s
  have hn : next.halted=false := running
  let stored := put (addressed next.core 13 output) .global (location s.core width output).toNat (s.core.regs 11)
  have hs : Block (storeCode 11 13 output) next.core stored :=
    run_sound (store_run next.core 11 13 output (by decide) (by decide) valid)
  let last : Kernel.State := {next with core:=stored}
  have ret : Exec ctx [.ret] last (halt last) := .stop hn (.simple (by simp)) rfl
  refine ⟨halt last,.next running (.simple (by simp)) hn (block_exec hs hn ret),rfl,?_⟩
  simp [last,stored,next,halt,Kernel.advance,put,addressed,assign,PTX.advance,simple,scalar,Nat.add_assoc]

end PtxTorchLean.Poisson.PTX.CellFinal

namespace PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.Witness

/-- Write-only tails always satisfy the byte-history recording policy; no
unperformed read is introduced when a thread stores its computed register. -/
theorem writes_recorded (memory : Space → Memory) (events : List (Event n))
    (writes : ∀ owner a, Event.data owner a∈events → a.data.store=true) :
    ByteHistory.Recorded memory events := by
  apply ByteHistory.reads_recorded
  intro r owner a found read
  have written := writes owner a (List.mem_of_getElem? found)
  simp [written] at read

theorem tail_lane (start : WithTail.State n) (thread : Fin n) (memory : Space → Memory)
    (running : start.halted thread=false) (fresh : start.core.barrier.arrived thread=false)
    (position : (start.core.lanes thread).pc=(WithOutput.front width).length+
      (if thread.val<width*width then 0 else 5))
    (valid : thread.val<width*width → Valid64 (start.core.lanes thread).globalStart
      (start.core.lanes thread).globalBytes (CellFinal.location (start.core.lanes thread) width output).toNat) :
    ∃ final events, WithTail.Runs cfg ctx (WithOutput.front width) (CellFinal.tail width output)
      start events (WithTail.update start thread final) ∧ ByteHistory.Recorded memory events ∧
      final.halted=true ∧ final.core.pc=(WithOutput.front width).length+6 := by
  by_cases active : thread.val<width*width
  · have pc : (start.core.lanes thread).pc=(WithOutput.front width).length := by simpa [active] using position
    obtain ⟨final,run,halted,done⟩ := CellFinal.tail_exists_complete (ctx:=ctx thread)
      (WithTail.lane start thread) running (valid active)
    obtain ⟨events,actual,writes⟩ := WithTail.tail_exec_lift (cfg:=cfg) (ctx:=ctx)
      (front:=WithOutput.front width) (tail:=CellFinal.tail width output) run fresh (by omega)
      (by intro j i found; simpa only [pc,Nat.sub_self,Nat.zero_add] using found)
      (by simp [CellFinal.tail,storeCode,addressCode,WithTail.noLoad])
    exact ⟨final,events,actual,writes_recorded memory events writes,halted,by simpa only [WithTail.lane,pc] using done⟩
  · have pc : (start.core.lanes thread).pc=(WithOutput.front width).length+5 := by simpa [active] using position
    have run : Kernel.Exec (ctx thread) [.ret] (WithTail.lane start thread) (Kernel.halt (WithTail.lane start thread)) :=
      .stop running (.simple (by simp)) rfl
    obtain ⟨events,actual,writes⟩ := WithTail.tail_exec_lift (cfg:=cfg) (ctx:=ctx)
      (front:=WithOutput.front width) (tail:=CellFinal.tail width output) run fresh (by omega)
      (by intro j i found; cases j <;> simp at found; cases found; simp [pc,CellFinal.tail,storeCode,addressCode])
      (by simp [WithTail.noLoad])
    exact ⟨_,events,actual,writes_recorded memory events writes,rfl,by simp [Kernel.halt,Kernel.advance,PTX.advance,WithTail.lane,pc,Nat.add_assoc]⟩

end PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.Witness

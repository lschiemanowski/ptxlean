import PoissonPTX.CellFinal

namespace PtxTorchLean.Poisson.PTX.CellFinal
open Kernel

def index (s : PTX.State) (width : Nat) : BitVec 32 :=
  u32 (s.regs 15)*BitVec.ofNat 32 (width*width)+u32 (s.regs 14)
def indexed (s : PTX.State) (width : Nat) : PTX.State := assign s 13 ((index s width).setWidth 64)
def location (s : PTX.State) (width : Nat) (output : Word) : Word := address (indexed s width) 13 output

def tail (width : Nat) (output : Word) : List Kernel.Instr :=
  [.mad32 13 15 (BitVec.ofNat 32 (width*width)) 14] ++
  (storeCode 11 13 output).map Kernel.Instr.data ++ [.ret]

def program (width : Nat) (b d output : Word) : List Kernel.Instr :=
  (arithmetic width b d).map Kernel.Instr.data ++ tail width output

theorem location_stable (stable : Contraction.Stable s t)
    (lane : t.regs 14=s.regs 14) (cell : t.regs 15=s.regs 15) : location t width output=location s width output := by
  have base : t.regs 0=s.regs 0 := by
    simp only [Contraction.Stable,Contraction.environment,Prod.mk.injEq] at stable
    exact stable.2.2.2.2.2.2.1
  simp [location,indexed,address,wide,index,assign,PTX.advance,lane,cell,base]

theorem tail_correct (running : s.halted=false)
    (valid : Valid64 s.core.globalStart s.core.globalBytes (location s.core width output).toNat)
    (execution : Exec ctx (tail width output) s final) :
    decode (read64 final.core.global (location s.core width output).toNat)=decode (s.core.regs 11) ∧
    final.core.shared=s.core.shared ∧
    (∀ p, p<(location s.core width output).toNat ∨ (location s.core width output).toNat+8≤p → final.core.global p=s.core.global p) ∧
    final.halted=true := by
  have rest := (exec_nonhalting_iff (i:=.mad32 13 15 (BitVec.ofNat 32 (width*width)) 14)
    (by simp) running (by simpa [simple,scalar] using running)).mp execution
  obtain ⟨middle,hstore,hret⟩ := exec_block rest
  have hv : Valid64 (indexed s.core width).globalStart (indexed s.core width).globalBytes
      (address (indexed s.core width) 13 output).toNat := valid
  have eq := store_block_eq hstore (by decide) (by decide) hv
  have returnRunning : ({simple ctx (.mad32 13 15 (BitVec.ofNat 32 (width*width)) 14) s with core:=middle} : Kernel.State).halted=false := running
  have returned := (exec_halting_iff (i:=.ret) (by simp) returnRunning rfl).mp hret
  subst final
  rw [eq]
  refine ⟨?_,rfl,?_,rfl⟩
  · simp [simple,halt,Kernel.advance,scalar,PTX.advance,put,indexed,index,location,addressed,assign]
  · intro p hp
    simpa [simple,halt,Kernel.advance,scalar,PTX.advance,put,indexed,index,location,addressed,assign] using
      write64_outside s.core.global (location s.core width output).toNat (s.core.regs 11) p hp

theorem tail_exists (s : Kernel.State) (running : s.halted=false)
    (valid : Valid64 s.core.globalStart s.core.globalBytes (location s.core width output).toNat) :
    ∃ final, Exec ctx (tail width output) s final := by
  let next := simple ctx (.mad32 13 15 (BitVec.ofNat 32 (width*width)) 14) s
  have hn : next.halted=false := running
  let stored := put (addressed next.core 13 output) .global (location s.core width output).toNat (s.core.regs 11)
  have hs : Block (storeCode 11 13 output) next.core stored :=
    run_sound (store_run next.core 11 13 output (by decide) (by decide) valid)
  let last : Kernel.State := {next with core:=stored}
  have ret : Exec ctx [.ret] last (halt last) := .stop hn (.simple (by simp)) rfl
  exact ⟨halt last,.next running (.simple (by simp)) hn (block_exec hs hn ret)⟩

/-- Complete final body, integer indexing and actual global store, including its
frame outside the output word. Inputs are bytes, not assumed tensor answers. -/
theorem correct (running : s.halted=false) (inputs : Inputs s.core width b d)
    (valid : Valid64 s.core.globalStart s.core.globalBytes (location s.core width output).toNat)
    (execution : Exec ctx (program width b d output) s final) :
    decode (read64 final.core.global (location s.core width output).toNat)=result s.core width b d ∧
    final.core.shared=s.core.shared ∧
    (∀ p, p<(location s.core width output).toNat ∨ (location s.core width output).toNat+8≤p → final.core.global p=s.core.global p) ∧
    final.halted=true := by
  obtain ⟨middle,body,rest⟩ := exec_block execution
  obtain ⟨value,frame,lane,cell⟩ := arithmetic_correct inputs body
  have loc := location_stable frame lane cell (width:=width) (output:=output)
  have fields := frame
  simp only [Contraction.Stable,Contraction.environment,Prod.mk.injEq] at fields
  obtain ⟨global,shared,gstart,gbytes,ss,sb,base,bs,row,col⟩ := fields
  have hv : Valid64 middle.globalStart middle.globalBytes (location middle width output).toNat := by
    simpa [gstart,gbytes,loc] using valid
  have h := tail_correct (s:={s with core:=middle}) (width:=width) (output:=output) running hv rest
  simpa only [loc,value,global,shared] using h

theorem execution_exists (s : Kernel.State) (running : s.halted=false) (inputs : Inputs s.core width b d)
    (valid : Valid64 s.core.globalStart s.core.globalBytes (location s.core width output).toNat) :
    ∃ final, Exec ctx (program width b d output) s final := by
  obtain ⟨middle,body⟩ := arithmetic_exists s.core inputs
  obtain ⟨value,frame,lane,cell⟩ := arithmetic_correct inputs body
  have loc := location_stable frame lane cell (width:=width) (output:=output)
  have fields := frame
  simp only [Contraction.Stable,Contraction.environment,Prod.mk.injEq] at fields
  obtain ⟨global,shared,gstart,gbytes,ss,sb,base,bs,row,col⟩ := fields
  obtain ⟨final,rest⟩ := tail_exists (ctx:=ctx) (width:=width) (output:=output) {s with core:=middle} running
    (by simpa [gstart,gbytes,loc] using valid)
  exact ⟨final,block_exec body running rest⟩

theorem fetched_correct (running : s.halted=false) (inputs : Inputs s.core width b d)
    (valid : Valid64 s.core.globalStart s.core.globalBytes (location s.core width output).toNat)
    (precode : List Kernel.Instr) (pc : s.core.pc=precode.length)
    (execution : Kernel.Run ctx (precode++program width b d output) s final) :
    decode (read64 final.core.global (location s.core width output).toNat)=result s.core width b d ∧
    final.core.shared=s.core.shared ∧
    (∀ p, p<(location s.core width output).toNat ∨ (location s.core width output).toNat+8≤p → final.core.global p=s.core.global p) ∧
    final.halted=true :=
  correct running inputs valid (run_exec execution precode _ rfl pc)

theorem fetched_exists (s : Kernel.State) (running : s.halted=false) (inputs : Inputs s.core width b d)
    (valid : Valid64 s.core.globalStart s.core.globalBytes (location s.core width output).toNat)
    (precode : List Kernel.Instr) (pc : s.core.pc=precode.length) :
    ∃ final, Kernel.Run ctx (precode++program width b d output) s final := by
  obtain ⟨final,run⟩ := execution_exists (ctx:=ctx) s running inputs valid
  exact ⟨final,exec_fetched run precode pc⟩

end PtxTorchLean.Poisson.PTX.CellFinal

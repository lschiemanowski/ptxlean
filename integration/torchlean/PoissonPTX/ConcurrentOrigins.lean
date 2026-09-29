import PoissonPTX.ConcurrentExec

namespace PtxTorchLean.Poisson.PTX.Concurrent

/-- Store records expose the actual source register expression and calculated
address, together with the allocation check performed by the instruction. -/
theorem store_origin (h : Data op s t (some access)) (store : access.data.store=true) :
    ∃ sp addr src, op=.store64 sp addr src ∧ access=⟨sp,⟨s.pc,true,(addr.eval s).toNat,src.eval s⟩⟩ ∧
      Valid64 (s.start sp) (s.bytes sp) (addr.eval s).toNat ∧
      t=put s sp (addr.eval s).toNat (src.eval s) := by
  cases h with
  | load => simp at store
  | store valid => exact ⟨_,_,_,rfl,rfl,valid,rfl⟩

theorem load_origin (h : Data op s t (some access)) (read : access.data.store=false) :
    ∃ sp dst addr, op=.load64 sp dst addr ∧
      access.space=sp ∧ access.data.pc=s.pc ∧ access.data.address=(addr.eval s).toNat ∧
      Valid64 (s.start sp) (s.bytes sp) (addr.eval s).toNat ∧
      t=assign s dst access.data.value := by
  cases h with
  | load valid => exact ⟨_,_,_,rfl,rfl,rfl,rfl,valid,rfl⟩
  | store => simp at read

/-- Padding skips the body and lands exactly at its barrier; it does not exit
or jump past synchronization. The combined guard represents the previously
computed lane comparison and its conditional forward branch. -/
theorem padding_guard (cfg : Config n) (program : List Instr) (s : State n) (thread : Fin n)
    (fresh : s.barrier.arrived thread=false)
    (guard : program[(s.lanes thread).pc]?=some (.skip active barrierPC))
    (padding : active≤thread.val) :
    Step cfg program thread s ⟨setLane s thread {s.lanes thread with pc:=barrierPC},[]⟩ := by
  refine ⟨fresh,_,guard,?_⟩
  have h := Dispatch.skip (cfg:=cfg) (thread:=thread) (s:=s) (active:=active) (target:=barrierPC)
  simpa [show ¬thread.val<active by omega] using h

theorem active_guard (cfg : Config n) (program : List Instr) (s : State n) (thread : Fin n)
    (fresh : s.barrier.arrived thread=false)
    (guard : program[(s.lanes thread).pc]?=some (.skip active barrierPC))
    (live : thread.val<active) :
    Step cfg program thread s ⟨setLane s thread (advance (s.lanes thread)),[]⟩ := by
  refine ⟨fresh,_,guard,?_⟩
  simpa [live,advance] using (Dispatch.skip (cfg:=cfg) (thread:=thread) (s:=s) (active:=active) (target:=barrierPC))

/-- Any memory record in one fetched step has an actual data-instruction origin. -/
theorem step_access_origin (h : Step cfg program thread s out)
    (member : Event.data owner access ∈ out.events) :
    owner=thread ∧ ∃ op next,
      program[(s.lanes thread).pc]?=some (.data op) ∧ Data op (s.lanes thread) next (some access) := by
  obtain ⟨fresh,i,fetch,dispatch⟩ := h
  cases dispatch with
  | data h =>
    cases ha : ‹Option Access› with
    | none => simp [ha] at member
    | some actual =>
      simp only [ha,Option.toList_some,List.map_cons,List.map_nil,List.mem_singleton,Event.data.injEq] at member
      obtain ⟨rfl,rfl⟩ := member
      exact ⟨rfl,_,_,fetch,by simpa only [ha] using h⟩
  | skip => simp at member
  | sync =>
    simp only [synchronize] at member
    split at member <;> simp_all

theorem padding_reaches_barrier (cfg : Config n) (program : List Instr) (s : State n) (thread : Fin n)
    (fresh : s.barrier.arrived thread=false)
    (guard : program[(s.lanes thread).pc]?=some (.skip active barrierPC))
    (padding : active≤thread.val) (barrier : program[barrierPC]?=some (.sync 0)) :
    ∃ next out, Step cfg program thread s ⟨next,[]⟩ ∧
      Step cfg program thread next out ∧ out=synchronize cfg next thread 0 := by
  let next := setLane s thread {s.lanes thread with pc:=barrierPC}
  refine ⟨next,synchronize cfg next thread 0,padding_guard cfg program s thread fresh guard padding,?_,rfl⟩
  exact ⟨fresh,_,by simpa [next,setLane] using barrier,Dispatch.sync⟩

/-- Locate any observed access in an actual execution prefix, rather than
accepting an externally fabricated access table. -/
theorem run_access_prefix (run : Runs cfg program start events final)
    (member : Event.data owner access ∈ events) :
    ∃ before earlier selected out suffix,
      Runs cfg program start earlier before ∧ Step cfg program selected before out ∧
      Event.data owner access ∈ out.events ∧ Runs cfg program out.state suffix final ∧
      events=earlier++out.events++suffix := by
  induction run with
  | nil => simp at member
  | @cons thread s out rest final step tail ih =>
    rcases List.mem_append.mp member with now | later
    · exact ⟨s,[],thread,out,rest,Runs.nil,step,now,tail,rfl⟩
    · obtain ⟨before,earlier,selected,next,suffix,hp,hs,hm,ht,he⟩ := ih later
      exact ⟨before,out.events++earlier,selected,next,suffix,Runs.cons step hp,hs,hm,ht,by simp [he,List.append_assoc]⟩

end PtxTorchLean.Poisson.PTX.Concurrent

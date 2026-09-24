import Ptx.SharedReductionMachine
import Ptx.SharedBarrierProgram

namespace Ptx.Scalar.SharedReduction.Machine

def resumed (s : State n) : State n :=
  {s with barrier := Barrier.reset 1, lanes := fun thread =>
    {s.lanes thread with block := .choose, scalar := {(s.lanes thread).scalar with pc := 0}}}

def barrierStage (s : State n) (count : Nat) : State n :=
  if count = n then resumed s else {s with barrier := Barrier.prefixState 0 count}

theorem barrier_stage_step (cfg : Config n) (s : State n)
    (ready : ∀ thread, Ready thread (s.lanes thread)) (count : Nat) (bound : count < n) :
    (step cfg none ⟨count,bound⟩ (barrierStage s count)).state = barrierStage s (count+1) := by
  let thread : Fin n := ⟨count,bound⟩
  let request : Barrier.Request n := ⟨⟨cfg.cta,0,0,5⟩,thread⟩
  have notFull : count ≠ n := by omega
  have same : request.key = Barrier.key (barrierConfig cfg) (Barrier.prefixState 0 count) := rfl
  have fresh : Barrier.Runnable (Barrier.prefixState 0 count) request.thread := by
    simp [Barrier.Runnable,Barrier.prefixState,request,thread]
  have marked : Barrier.mark (Barrier.prefixState 0 count) request.thread = Barrier.prefixState 0 (count+1) :=
    Barrier.mark_prefix 0 count bound
  have protocol : Barrier.step (barrierConfig cfg) (Barrier.prefixState 0 count) request =
      if count+1 = n then ⟨Barrier.reset 1,.released,[.arrival request.key thread,.completion request.key]⟩
      else ⟨Barrier.prefixState 0 (count+1),.waiting,[.arrival request.key thread]⟩ := by
    by_cases last : count+1 = n
    · have complete : Barrier.Complete (Barrier.mark (Barrier.prefixState 0 count) request.thread) := by
        rw [marked,Barrier.complete_prefix_iff (barrierConfig cfg)]; omega
      simpa [last,Barrier.prefixState] using Barrier.completing_step (barrierConfig cfg) _ request same fresh complete
    · have incomplete : ¬Barrier.Complete (Barrier.mark (Barrier.prefixState 0 count) request.thread) := by
        rw [marked,Barrier.complete_prefix_iff (barrierConfig cfg)]; omega
      simpa [last,marked] using Barrier.waiting_step (barrierConfig cfg) _ request same fresh incomplete
  have h := ready thread
  simp only [Ready] at h
  have fetch : step cfg none thread (barrierStage s count) =
      dispatch cfg none thread (.sync 0) {s with barrier := Barrier.prefixState 0 count} := by
    simp [step,barrierStage,notFull,h.1,h.2.1,h.2.2.2,program]
  rw [show (⟨count,bound⟩ : Fin n) = thread from rfl,fetch]
  have requestEq : barrierRequest cfg {s with barrier := Barrier.prefixState 0 count} thread 0 = request := rfl
  simp only [dispatch,requestEq]
  rw [protocol]
  by_cases last : count+1 = n <;> simp [last,barrierStage,resumed]

theorem barrier_prefix (cfg : Config n) (s : State n)
    (ready : ∀ thread, Ready thread (s.lanes thread)) (count : Nat) (bound : count ≤ n) :
    (run cfg (SharedBarrier.prefixSchedule count bound) (barrierStage s 0)).state = barrierStage s count := by
  induction count with
  | zero => rfl
  | succ count ih =>
    simp only [SharedBarrier.prefixSchedule,run_append]
    rw [ih (by omega)]
    simpa [run,runWith] using barrier_stage_step cfg s ready count (by omega)

theorem barrier_round (cfg : Config n) (s : State n)
    (ready : ∀ thread, Ready thread (s.lanes thread)) (initial : s.barrier = Barrier.initial) :
    (run cfg (SharedBarrier.schedule n) s).state = resumed s := by
  have startEq : barrierStage s 0 = s := by
    have nonzero : 0 ≠ n := by have := cfg.nonempty; omega
    simp only [barrierStage,ite_eq_right (by exact nonzero),Barrier.prefix_zero]
    change {s with barrier := Barrier.initial} = s
    rw [← initial]
  have h := barrier_prefix cfg s ready n (Nat.le_refl n)
  rw [startEq] at h
  simpa [SharedBarrier.schedule,barrierStage] using h



/-- After a completed barrier, nonleaders execute the guard and explicit exit. -/
theorem follower_exit (cfg : Config n) (s : State n) (thread : Fin n)
    (block : (s.lanes thread).block = .choose) (pc : (s.lanes thread).scalar.pc = 0)
    (live : (s.lanes thread).halted = false)
    (laneId : (s.lanes thread).scalar.regs 0 = BitVec.ofNat 32 thread.val)
    (notLeader : thread.val ≠ 0) :
    let final := (run cfg (List.replicate 3 thread) s).state
    (final.lanes thread).halted = true ∧ final.global = s.global ∧
      final.shared = s.shared ∧ final.barrier = s.barrier ∧
      ∀ other, other ≠ thread → final.lanes other = s.lanes other := by
  have fits : thread.val < 2^32 := by have := cfg.noWrap; have := thread.isLt; omega
  have nz : (BitVec.ofNat 32 thread.val : Word) ≠ 0 := by
    intro h
    have natEq := congrArg BitVec.toNat h
    simp [Nat.mod_eq_of_lt fits] at natEq
    exact notLeader natEq
  change (BitVec.ofNat 32 thread.val : Word) ≠ 0#32 at nz
  simp [run,runWith,List.replicate,step,dispatch,scalarStep,program,setLane,block,pc,live,
    eval,Instr.plain,Guard.eval,Compare.eval,Operand32.eval,laneId,nz,update]
  intro other different
  simp [different]

/-- Leader initialization is three actual moves, followed by an actual branch;
its previous accumulator, counter and pointer registers are not premises. -/
theorem leader_initialize (cfg : Config n) (s : State n) (thread : Fin n)
    (block : (s.lanes thread).block = .choose) (pc : (s.lanes thread).scalar.pc = 0)
    (live : (s.lanes thread).halted = false) (laneId : (s.lanes thread).scalar.regs 0 = 0) :
    let final := (run cfg (List.replicate 6 thread) s).state
    (final.lanes thread).block = .loop ∧ (final.lanes thread).scalar.pc = 0 ∧
    (final.lanes thread).scalar.regs 0 = BitVec.ofNat 32 n ∧
    (final.lanes thread).scalar.regs 1 = 0 ∧ (final.lanes thread).scalar.addrs 0 = 0 ∧
    (final.lanes thread).halted = false ∧ final.global = s.global ∧
      final.shared = s.shared ∧ final.barrier = s.barrier ∧
      ∀ other, other ≠ thread → final.lanes other = s.lanes other := by
  simp [run,runWith,List.replicate,step,dispatch,scalarStep,program,setLane,block,pc,live,
    eval,Instr.plain,Guard.eval,Compare.eval,Operand32.eval,Operand64.eval,laneId,update]
  intro other different
  simp [different]



def loopNext (s : State n) (thread : Fin n) (value : Word) : State n :=
  setLane s thread {(s.lanes thread) with scalar := (Kernels.loopNext {(s.lanes thread).scalar with memory := s.shared} value)}

theorem loop_seven (cfg : Config n) (s : State n) (thread : Fin n)
    (block : (s.lanes thread).block = .loop) (pc : (s.lanes thread).scalar.pc = 0)
    (live : (s.lanes thread).halted = false) (count : (s.lanes thread).scalar.regs 0 ≠ 0)
    (address : addressIndex s.shared ((s.lanes thread).scalar.addrs 0) = .ok index) :
    (run cfg (List.replicate 7 thread) s).state = loopNext s thread s.shared[index]! := by
  change (s.lanes thread).scalar.regs 0 ≠ 0#32 at count
  have test : ((s.lanes thread).scalar.regs 0 == 0#32) = false := by simp [count]
  simp [run,runWith,List.replicate,step,dispatch,scalarStep,program,setLane,block,pc,live,
    eval,Instr.plain,Guard.eval,Compare.eval,Operand32.eval,Operand64.eval,BinOp.eval,
    test,update,address,loopNext,Kernels.loopNext]
  funext other
  by_cases same : other = thread <;> simp [same]

theorem loop_zero (cfg : Config n) (s : State n) (thread : Fin n)
    (block : (s.lanes thread).block = .loop) (pc : (s.lanes thread).scalar.pc = 0)
    (live : (s.lanes thread).halted = false) (count : (s.lanes thread).scalar.regs 0 = 0) :
    let final := (run cfg (List.replicate 3 thread) s).state
    (final.lanes thread).block = .output ∧ (final.lanes thread).scalar.pc = 0 ∧
    (final.lanes thread).scalar.regs 1 = (s.lanes thread).scalar.regs 1 ∧
    (final.lanes thread).halted = false ∧ final.global = s.global ∧
      final.shared = s.shared ∧ final.barrier = s.barrier ∧
      ∀ other, other ≠ thread → final.lanes other = s.lanes other := by
  simp [run,runWith,List.replicate,step,dispatch,scalarStep,program,setLane,block,pc,live,
    eval,Instr.plain,Guard.eval,Compare.eval,Operand32.eval,count,update]
  intro other different
  simp [different]

/-- The actual repeated-PC loop terminates in the output block after all loads.
Every arithmetic result is obtained from Scalar.eval, with modular addition. -/
theorem loop_execution (cfg : Config n) (s : State n) (thread : Fin n)
    (block : (s.lanes thread).block = .loop) (pc : (s.lanes thread).scalar.pc = 0)
    (live : (s.lanes thread).halted = false) (count startIndex : Nat)
    (counter : (s.lanes thread).scalar.regs 0 = BitVec.ofNat 32 count)
    (pointer : (s.lanes thread).scalar.addrs 0 = bytePointer startIndex)
    (extent : startIndex+count ≤ s.shared.length)
    (countFits : count < 2^32) (addressFits : 4*(startIndex+count) < 2^64) :
    let final := (run cfg (List.replicate (7*count+3) thread) s).state
    (final.lanes thread).block = .output ∧ (final.lanes thread).scalar.pc = 0 ∧
    (final.lanes thread).scalar.regs 1 =
      Kernels.sliceSum s.shared startIndex count ((s.lanes thread).scalar.regs 1) ∧
    (final.lanes thread).halted = false ∧ final.global = s.global ∧
      final.shared = s.shared ∧ final.barrier = s.barrier ∧
      ∀ other, other ≠ thread → final.lanes other = s.lanes other := by
  induction count generalizing s startIndex with
  | zero => simpa [Kernels.sliceSum] using loop_zero cfg s thread block pc live counter
  | succ count ih =>
    have inside : startIndex < s.shared.length := by omega
    have addressNat : ((s.lanes thread).scalar.addrs 0).toNat = 4*startIndex := by
      rw [pointer]; simp only [bytePointer,BitVec.toNat_ofNat]
      exact Nat.mod_eq_of_lt (by omega)
    have indexOK : addressIndex s.shared ((s.lanes thread).scalar.addrs 0) = .ok startIndex := by
      simp [addressIndex,addressNat,inside]
    have nonzero : (s.lanes thread).scalar.regs 0 ≠ 0 := by
      intro h
      have e := congrArg BitVec.toNat h
      rw [counter] at e
      simp only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt countFits] at e
      change count+1 = 0 at e
      omega
    let next := loopNext s thread s.shared[startIndex]!
    have nextCounter : (next.lanes thread).scalar.regs 0 = BitVec.ofNat 32 count := by
      simp only [next,loopNext,setLane_same,Kernels.loopNext,update_same,counter]
      change BitVec.ofNat 32 (count+1) - BitVec.ofNat 32 1 = _
      rw [BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) (by omega)]
      simp
    have nextPointer : (next.lanes thread).scalar.addrs 0 = bytePointer (startIndex+1) := by
      simp only [next,loopNext,setLane_same,Kernels.loopNext,update_same,pointer]
      change BitVec.ofNat 64 (4*startIndex) + BitVec.ofNat 64 4 = _
      rw [← BitVec.ofNat_add]; congr 1
    have ihResult := ih next (by simpa [next,loopNext] using block) (by simp [next,loopNext,Kernels.loopNext])
      (by simpa [next,loopNext] using live) (startIndex+1) nextCounter nextPointer
      (by change startIndex+1+count ≤ s.shared.length; omega) (by omega) (by omega)
    have budget : 7*(count+1)+3 = 7+(7*count+3) := by omega
    dsimp only
    rw [budget,← List.replicate_append_replicate,run_append]
    dsimp only
    rw [loop_seven cfg s thread block pc live nonzero indexOK]
    refine ⟨ihResult.1,ihResult.2.1,?_,ihResult.2.2.2.1,ihResult.2.2.2.2.1,
      ihResult.2.2.2.2.2.1,ihResult.2.2.2.2.2.2.1,?_⟩
    · rw [ihResult.2.2.1]
      simp only [Kernels.sliceSum,next,loopNext,setLane_same,Kernels.loopNext,update]
      rw [List.drop_eq_getElem_cons inside]
      simp [inside,setLane,-List.getElem_cons_drop]
    · intro other different
      exact (ihResult.2.2.2.2.2.2.2 other different).trans (setLane_other s thread other _ different)



/-- The final fetched global store updates only the output word after all loads. -/
theorem output_phase (cfg : Config n) (s : State n) (thread : Fin n)
    (block : (s.lanes thread).block = .output) (pc : (s.lanes thread).scalar.pc = 0)
    (live : (s.lanes thread).halted = false) (extent : n < s.global.length) :
    let final := (run cfg (List.replicate 2 thread) s).state
    (final.lanes thread).halted = true ∧
    final.global = s.global.set n ((s.lanes thread).scalar.regs 1) ∧
    final.shared = s.shared ∧ final.barrier = s.barrier ∧
      ∀ other, other ≠ thread → final.lanes other = s.lanes other := by
  have fits : 4*n < 2^64 := by have := cfg.noWrap; omega
  have index : addressIndex s.global (bytePointer n) = .ok n := by
    simp [addressIndex,bytePointer,Nat.mod_eq_of_lt fits,extent]
  simp [run,runWith,List.replicate,step,dispatch,scalarStep,program,setLane,block,pc,live,
    eval,Instr.plain,Guard.eval,Operand32.eval,Operand64.eval,index]
  intro other different
  simp [different]

/-- A leader executes election, initialization, every loop iteration, the output
store and explicit exit. Other lanes and scratch are unchanged by this phase. -/
theorem leader_phase (cfg : Config n) (s : State n) (thread : Fin n)
    (block : (s.lanes thread).block = .choose) (pc : (s.lanes thread).scalar.pc = 0)
    (live : (s.lanes thread).halted = false) (laneId : (s.lanes thread).scalar.regs 0 = 0)
    (globalExtent : n < s.global.length) (sharedExtent : n ≤ s.shared.length) :
    let final := (run cfg (List.replicate (6+(7*n+3)+2) thread) s).state
    (final.lanes thread).halted = true ∧ final.global = s.global.set n (total s.shared n) ∧
    final.shared = s.shared ∧ final.barrier = s.barrier ∧
      ∀ other, other ≠ thread → final.lanes other = s.lanes other := by
  let initialized := (run cfg (List.replicate 6 thread) s).state
  obtain ⟨ib,ip,ic,ia,iad,il,ig,is,ibar,io⟩ := leader_initialize cfg s thread block pc live laneId
  change initialized.shared = s.shared at is
  change initialized.global = s.global at ig
  change (initialized.lanes thread).scalar.regs 1 = 0 at ia
  let summed := (run cfg (List.replicate (7*n+3) thread) initialized).state
  have fits : n < 2^32 := by have := cfg.noWrap; omega
  have pfits : 4*n < 2^64 := by have := cfg.noWrap; omega
  obtain ⟨sb,sp,sv,sl,sg,ss,sbar,so⟩ := loop_execution cfg initialized thread ib ip il n 0 ic iad
    (by change 0+n ≤ initialized.shared.length; rw [is]; simpa using sharedExtent) fits (by simpa using pfits)
  have summedValue : (summed.lanes thread).scalar.regs 1 = total s.shared n := by
    change (summed.lanes thread).scalar.regs 1 = Kernels.sliceSum initialized.shared 0 n ((initialized.lanes thread).scalar.regs 1) at sv
    simpa only [Kernels.sliceSum,List.drop_zero,ia,is,total] using sv
  change summed.global = initialized.global at sg
  have result := output_phase cfg summed thread sb sp sl (by rw [sg,ig]; exact globalExtent)
  dsimp only
  rw [← List.replicate_append_replicate,run_append]
  dsimp only
  rw [← List.replicate_append_replicate,run_append]
  dsimp only
  change ((run cfg (List.replicate 2 thread) summed).state.lanes thread).halted = true ∧ _
  refine ⟨result.1,?_,result.2.2.1.trans (ss.trans is),result.2.2.2.1.trans (sbar.trans ibar),?_⟩
  · exact result.2.1.trans (by rw [summedValue,sg,ig])
  · intro other different
    exact (result.2.2.2.2 other different).trans ((so other different).trans (io other different))



/-- Scheduling the nonleader exits never changes the leader or any memory. -/
theorem followers_phase (cfg : Config n) (s : State n) (lanes : List (Fin n))
    (distinct : lanes.Nodup)
    (ready : ∀ thread ∈ lanes, (s.lanes thread).block = .choose ∧
      (s.lanes thread).scalar.pc = 0 ∧ (s.lanes thread).halted = false ∧
      (s.lanes thread).scalar.regs 0 = BitVec.ofNat 32 thread.val ∧ thread.val ≠ 0) :
    let final := (run cfg (lanes.flatMap (List.replicate 3)) s).state
    final.global = s.global ∧ final.shared = s.shared ∧ final.barrier = s.barrier ∧
    (∀ thread ∈ lanes, (final.lanes thread).halted = true) ∧
    (∀ other, other ∉ lanes → final.lanes other = s.lanes other) := by
  induction lanes generalizing s with
  | nil => simp [run,runWith]
  | cons lane rest ih =>
    have unique := List.nodup_cons.mp distinct
    obtain ⟨b,p,l,r,nonzero⟩ := ready lane (by simp)
    obtain ⟨halt,g,sh,bar,others⟩ := follower_exit cfg s lane b p l r nonzero
    let mid := (run cfg (List.replicate 3 lane) s).state
    have restReady : ∀ thread ∈ rest, (mid.lanes thread).block = .choose ∧
        (mid.lanes thread).scalar.pc = 0 ∧ (mid.lanes thread).halted = false ∧
        (mid.lanes thread).scalar.regs 0 = BitVec.ofNat 32 thread.val ∧ thread.val ≠ 0 := by
      intro thread member
      have different : thread ≠ lane := by intro h; subst thread; exact unique.1 member
      rw [show mid.lanes thread = s.lanes thread from others thread different]
      exact ready thread (by simp [member])
    have ihResult := ih mid unique.2 restReady
    dsimp only at ihResult ⊢
    rw [List.flatMap_cons,run_append]
    dsimp only
    refine ⟨ihResult.1.trans g,ihResult.2.1.trans sh,ihResult.2.2.1.trans bar,?_,?_⟩
    · intro thread member
      rcases List.mem_cons.mp member with same | remaining
      · subst thread
        exact (congrArg Lane.halted (ihResult.2.2.2.2 lane unique.1)).trans halt
      · exact ihResult.2.2.2.1 thread remaining
    · intro other absent
      have different : other ≠ lane := by intro h; subst other; exact absent (by simp)
      have outside : other ∉ rest := by intro h; exact absent (by simp [h])
      exact (ihResult.2.2.2.2 other outside).trans (others other different)

def followers (n : Nat) : List (Fin n) := (List.finRange n).filter (fun t => t.val != 0)

def fullSchedule (cfg : Config n) : List (Fin n) :=
  producerSchedule (List.finRange n) ++ SharedBarrier.schedule n ++
    (followers n).flatMap (List.replicate 3) ++ List.replicate (6+(7*n+3)+2) ⟨0,cfg.nonempty⟩

/-- An actual fetched whole-program execution terminates with the modular sum.
The only entry bindings are the initial lane IDs, input/storage and arbitrary seeds. -/
theorem full_execution (cfg : Config n) (input scratch : List Word) (seeds : Fin n → Seed)
    (inputs : n < input.length) (storage : n ≤ scratch.length) :
    let final := (run cfg (fullSchedule cfg) (start input scratch seeds)).state
    final.global = input.set n (total input n) ∧
    final.shared = input.take n ++ scratch.drop n ∧
    final.barrier = Barrier.reset 1 ∧ ∀ thread, (final.lanes thread).halted = true := by
  let initial := start input scratch seeds
  let produced := (run cfg (producerSchedule (List.finRange n)) initial).state
  obtain ⟨pg,ps,pbar,pr⟩ := producer_round cfg input scratch seeds (by omega) storage
  have barrierEq := barrier_round cfg produced pr pbar
  let released := resumed produced
  have releasedGlobal : released.global = input := pg
  have releasedShared : released.shared = input.take n ++ scratch.drop n := ps
  have ready : ∀ thread ∈ followers n, (released.lanes thread).block = .choose ∧
      (released.lanes thread).scalar.pc = 0 ∧ (released.lanes thread).halted = false ∧
      (released.lanes thread).scalar.regs 0 = BitVec.ofNat 32 thread.val ∧ thread.val ≠ 0 := by
    intro thread member
    have nonzero : thread.val ≠ 0 := by simpa [followers] using member
    exact ⟨rfl,rfl,(pr thread).2.2.2,(pr thread).2.2.1,nonzero⟩
  have distinct : (followers n).Nodup := List.Pairwise.filter _ (List.nodup_finRange n)
  let exited := (run cfg ((followers n).flatMap (List.replicate 3)) released).state
  obtain ⟨eg,es,eb,eh,eo⟩ := followers_phase cfg released (followers n) distinct ready
  let leader : Fin n := ⟨0,cfg.nonempty⟩
  have leaderAbsent : leader ∉ followers n := by simp [followers,leader]
  have untouched : exited.lanes leader = released.lanes leader := eo leader leaderAbsent
  have leaderReady : (exited.lanes leader).block = .choose ∧
      (exited.lanes leader).scalar.pc = 0 ∧ (exited.lanes leader).halted = false ∧
      (exited.lanes leader).scalar.regs 0 = 0 := by
    rw [untouched]
    exact ⟨rfl,rfl,(pr leader).2.2.2,(pr leader).2.2.1⟩
  obtain ⟨lh,lg,ls,lb,lo⟩ := leader_phase cfg exited leader leaderReady.1 leaderReady.2.1
    leaderReady.2.2.1 leaderReady.2.2.2
    (by rw [eg,releasedGlobal]; exact inputs)
    (by rw [es,releasedShared]; simp only [List.length_append,List.length_take,List.length_drop]; omega)
  have totalEq : total exited.shared n = total input n := by
    rw [es,releasedShared]
    simp [total,List.length_take,Nat.min_eq_left (by omega : n ≤ input.length)]
  dsimp only
  simp only [fullSchedule,run_append]
  rw [barrierEq]
  refine ⟨?_,ls.trans (es.trans releasedShared),lb.trans eb,?_⟩
  · rw [lg,totalEq,eg,releasedGlobal]
  · intro thread
    by_cases same : thread = leader
    · subst thread; exact lh
    · have member : thread ∈ followers n := by
        have nonzero : thread.val ≠ 0 := by intro h; exact same (Fin.ext h)
        simp [followers,nonzero]
      exact (congrArg Lane.halted (lo thread same)).trans (eh thread member)

end Ptx.Scalar.SharedReduction.Machine

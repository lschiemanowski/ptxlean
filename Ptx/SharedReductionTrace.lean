import Ptx.SharedReductionProgram

namespace Ptx.Scalar.SharedReduction.Machine

abbrev Access (n : Nat) := Space × Fin n × MemoryEffect

def memoryEvent : Event n → Option (Access n)
  | .scalar thread _ (some space) event => event.memory.map (fun effect => (space,thread,effect))
  | _ => none

def accesses (trace : List (Event n)) : List (Access n) := trace.filterMap memoryEvent

@[simp] theorem accesses_append (left right : List (Event n)) :
    accesses (left++right) = accesses left ++ accesses right := List.filterMap_append

/-- Labels below describe the proven projection of actual execution, not a substitute runner. -/
def producerAccesses (input : List Word) (thread : Fin n) : List (Access n) :=
  [(.global,thread,⟨.load,bytePointer thread.val,input[thread.val]!⟩),
   (.shared,thread,⟨.store,bytePointer thread.val,input[thread.val]!⟩)]

theorem producer_accesses (cfg : Config n) (s : State n) (thread : Fin n) (seed : Seed)
    (entry : s.lanes thread = ⟨.producer,producerStart s.global thread seed,false⟩)
    (inputs : n ≤ s.global.length) (storage : n ≤ s.shared.length) :
    accesses (run cfg (List.replicate 7 thread) s).trace = producerAccesses s.global thread := by
  have fits : thread.val < 2^32 := by have := cfg.noWrap; have := thread.isLt; omega
  have pfits : 4*thread.val < 2^64 := by have := cfg.noWrap; have := thread.isLt; omega
  have double : (BitVec.ofNat 64 thread.val + BitVec.ofNat 64 thread.val : Address) =
      BitVec.ofNat 64 (2*thread.val) := by rw [← BitVec.ofNat_add]; congr 1; omega
  have four : (BitVec.ofNat 64 (2*thread.val) + BitVec.ofNat 64 (2*thread.val) : Address) =
      bytePointer thread.val := by rw [← BitVec.ofNat_add]; simp [bytePointer]; congr 1; omega
  have gi : addressIndex s.global (bytePointer thread.val) = .ok thread.val := by
    simp [addressIndex,bytePointer,Nat.mod_eq_of_lt pfits,show thread.val < s.global.length by have := thread.isLt; omega]
  have si : addressIndex s.shared (bytePointer thread.val) = .ok thread.val := by
    simp [addressIndex,bytePointer,Nat.mod_eq_of_lt pfits,show thread.val < s.shared.length by have := thread.isLt; omega]
  simp [accesses,memoryEvent,List.filterMap,producerAccesses,run,runWith,List.replicate,step,dispatch,scalarStep,program,setLane,entry,
    producerStart,eval,Instr.plain,Guard.eval,Operand32.eval,Operand64.eval,update,
    Nat.mod_eq_of_lt fits,double,four,gi,si,sharedStore,occurrence]

theorem producer_list_accesses (cfg : Config n) (s : State n) (seeds : Fin n → Seed)
    (lanes : List (Fin n)) (distinct : lanes.Nodup)
    (entry : ∀ lane ∈ lanes, s.lanes lane = ⟨.producer,producerStart s.global lane (seeds lane),false⟩)
    (inputs : n ≤ s.global.length) (storage : n ≤ s.shared.length) :
    accesses (run cfg (producerSchedule lanes) s).trace = lanes.flatMap (producerAccesses s.global) := by
  induction lanes generalizing s with
  | nil => rfl
  | cons lane rest ih =>
    have unique := List.nodup_cons.mp distinct
    let mid := (run cfg (List.replicate 7 lane) s).state
    obtain ⟨g,sh,_,_,_,_,_,other⟩ := producer_phase cfg s lane (seeds lane) (entry lane (by simp)) inputs storage
    have entries : ∀ t ∈ rest, mid.lanes t = ⟨.producer,producerStart mid.global t (seeds t),false⟩ := by
      intro t member
      have different : t ≠ lane := by intro h; subst t; exact unique.1 member
      rw [show mid.lanes t = s.lanes t from other t different,show mid.global = s.global from g]
      exact entry t (by simp [member])
    have tail := ih mid unique.2 entries (by change n ≤ mid.global.length; rw [show mid.global = s.global from g]; exact inputs)
      (by change n ≤ mid.shared.length; rw [show mid.shared = _ from sh]; simpa using storage)
    simp only [producerSchedule,List.flatMap_cons,run_append]
    change accesses ((run cfg (List.replicate 7 lane) s).trace ++
      (run cfg (producerSchedule rest) mid).trace) = _
    rw [accesses_append,producer_accesses cfg s lane (seeds lane) (entry lane (by simp)) inputs storage,tail]
    rw [show mid.global = s.global from g]

theorem loop_seven_accesses (cfg : Config n) (s : State n) (thread : Fin n)
    (block : (s.lanes thread).block = .loop) (pc : (s.lanes thread).scalar.pc = 0)
    (live : (s.lanes thread).halted = false) (count : (s.lanes thread).scalar.regs 0 ≠ 0)
    (address : addressIndex s.shared ((s.lanes thread).scalar.addrs 0) = .ok index) :
    accesses (run cfg (List.replicate 7 thread) s).trace =
      [(.shared,thread,⟨.load,(s.lanes thread).scalar.addrs 0,s.shared[index]!⟩)] := by
  change (s.lanes thread).scalar.regs 0 ≠ 0#32 at count
  have test : ((s.lanes thread).scalar.regs 0 == 0#32) = false := by simp [count]
  simp [accesses,memoryEvent,List.filterMap,run,runWith,List.replicate,step,dispatch,scalarStep,program,setLane,block,pc,live,
    eval,Instr.plain,Guard.eval,Compare.eval,Operand32.eval,Operand64.eval,BinOp.eval,
    test,update,address,occurrence]

theorem loop_zero_accesses (cfg : Config n) (s : State n) (thread : Fin n)
    (block : (s.lanes thread).block = .loop) (pc : (s.lanes thread).scalar.pc = 0)
    (live : (s.lanes thread).halted = false) (count : (s.lanes thread).scalar.regs 0 = 0) :
    accesses (run cfg (List.replicate 3 thread) s).trace = [] := by
  simp [accesses,memoryEvent,List.filterMap,run,runWith,List.replicate,step,dispatch,scalarStep,program,setLane,block,pc,live,
    eval,Instr.plain,Guard.eval,Compare.eval,Operand32.eval,count,update,occurrence]

def loopAccesses (scratch : List Word) (thread : Fin n) (start count : Nat) : List (Access n) :=
  (List.range count).map (fun i => (.shared,thread,⟨.load,bytePointer (start+i),scratch[start+i]!⟩))

theorem loop_accesses (cfg : Config n) (s : State n) (thread : Fin n)
    (block : (s.lanes thread).block = .loop) (pc : (s.lanes thread).scalar.pc = 0)
    (live : (s.lanes thread).halted = false) (count startIndex : Nat)
    (counter : (s.lanes thread).scalar.regs 0 = BitVec.ofNat 32 count)
    (pointer : (s.lanes thread).scalar.addrs 0 = bytePointer startIndex)
    (extent : startIndex+count ≤ s.shared.length)
    (countFits : count < 2^32) (addressFits : 4*(startIndex+count) < 2^64) :
    accesses (run cfg (List.replicate (7*count+3) thread) s).trace =
      loopAccesses s.shared thread startIndex count := by
  induction count generalizing s startIndex with
  | zero => simpa [loopAccesses] using loop_zero_accesses cfg s thread block pc live counter
  | succ count ih =>
    have inside : startIndex < s.shared.length := by omega
    have addressNat : ((s.lanes thread).scalar.addrs 0).toNat = 4*startIndex := by
      rw [pointer]; simp only [bytePointer,BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
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
      rw [BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) (by omega)]; simp
    have nextPointer : (next.lanes thread).scalar.addrs 0 = bytePointer (startIndex+1) := by
      simp only [next,loopNext,setLane_same,Kernels.loopNext,update_same,pointer]
      change BitVec.ofNat 64 (4*startIndex) + BitVec.ofNat 64 4 = _
      rw [← BitVec.ofNat_add]; congr 1
    have tail := ih next (by simpa [next,loopNext] using block)
      (by simp [next,loopNext,Kernels.loopNext]) (by simpa [next,loopNext] using live)
      (startIndex+1) nextCounter nextPointer (by change startIndex+1+count ≤ s.shared.length; omega)
      (by omega) (by omega)
    have budget : 7*(count+1)+3 = 7+(7*count+3) := by omega
    rw [budget,← List.replicate_append_replicate,run_append]
    change accesses ((run cfg (List.replicate 7 thread) s).trace ++
      (run cfg (List.replicate (7*count+3) thread) (run cfg (List.replicate 7 thread) s).state).trace) = _
    rw [accesses_append,loop_seven_accesses cfg s thread block pc live nonzero indexOK,
      loop_seven cfg s thread block pc live nonzero indexOK,tail,pointer]
    simp only [loopAccesses,next,loopNext,setLane]
    rw [List.range_succ_eq_map]
    simp [List.map_map,Function.comp_def,Nat.add_comm,Nat.add_left_comm]



theorem sync_no_accesses (cfg : Config n) (s : State n) (thread : Fin n) (resource : Fin 16) :
    accesses (dispatch cfg none thread (.sync resource) s).events = [] := by
  simp only [dispatch]
  split <;> simp [accesses,memoryEvent,List.filterMap_map,Function.comp_def]

theorem barrier_prefix_accesses (cfg : Config n) (s : State n)
    (ready : ∀ thread, Ready thread (s.lanes thread)) (count : Nat) (bound : count ≤ n) :
    accesses (run cfg (SharedBarrier.prefixSchedule count bound) (barrierStage s 0)).trace = [] := by
  induction count with
  | zero => rfl
  | succ count ih =>
    have below : count < n := by omega
    let thread : Fin n := ⟨count,below⟩
    have h := ready thread
    have notFull : count ≠ n := by omega
    have fetch : step cfg none thread (barrierStage s count) =
        dispatch cfg none thread (.sync 0) (barrierStage s count) := by
      simp [step,barrierStage,notFull,h.1,h.2.1,h.2.2.2,program]
    simp only [SharedBarrier.prefixSchedule,run_append]
    change accesses ((run cfg (SharedBarrier.prefixSchedule count (by omega)) (barrierStage s 0)).trace ++
      (run cfg [thread] (run cfg (SharedBarrier.prefixSchedule count (by omega)) (barrierStage s 0)).state).trace) = []
    rw [accesses_append,ih,barrier_prefix cfg s ready count (by omega)]
    simp only [run,runWith,List.append_nil,List.nil_append]
    rw [fetch]
    exact sync_no_accesses cfg _ thread 0

theorem barrier_round_accesses (cfg : Config n) (s : State n)
    (ready : ∀ thread, Ready thread (s.lanes thread)) (initial : s.barrier = Barrier.initial) :
    accesses (run cfg (SharedBarrier.schedule n) s).trace = [] := by
  have startEq : barrierStage s 0 = s := by
    have nonzero : 0 ≠ n := by have := cfg.nonempty; omega
    simp only [barrierStage,ite_eq_right (by exact nonzero),Barrier.prefix_zero]
    change {s with barrier := Barrier.initial} = s
    rw [← initial]
  have h := barrier_prefix_accesses cfg s ready n (Nat.le_refl n)
  rw [startEq] at h
  exact h

theorem follower_no_accesses (cfg : Config n) (s : State n) (thread : Fin n)
    (block : (s.lanes thread).block = .choose) (pc : (s.lanes thread).scalar.pc = 0)
    (live : (s.lanes thread).halted = false)
    (laneId : (s.lanes thread).scalar.regs 0 = BitVec.ofNat 32 thread.val)
    (notLeader : thread.val ≠ 0) :
    accesses (run cfg (List.replicate 3 thread) s).trace = [] := by
  have fits : thread.val < 2^32 := by have := cfg.noWrap; have := thread.isLt; omega
  have nz : (BitVec.ofNat 32 thread.val : Word) ≠ 0#32 := by
    intro h
    have natEq := congrArg BitVec.toNat h
    simp [Nat.mod_eq_of_lt fits] at natEq
    exact notLeader natEq
  simp [accesses,memoryEvent,List.filterMap,run,runWith,List.replicate,step,dispatch,scalarStep,program,setLane,block,pc,live,
    eval,Instr.plain,Guard.eval,Compare.eval,Operand32.eval,laneId,nz,update,occurrence]

theorem initialize_no_accesses (cfg : Config n) (s : State n) (thread : Fin n)
    (block : (s.lanes thread).block = .choose) (pc : (s.lanes thread).scalar.pc = 0)
    (live : (s.lanes thread).halted = false) (laneId : (s.lanes thread).scalar.regs 0 = 0) :
    accesses (run cfg (List.replicate 6 thread) s).trace = [] := by
  simp [accesses,memoryEvent,List.filterMap,run,runWith,List.replicate,step,dispatch,scalarStep,program,setLane,block,pc,live,
    eval,Instr.plain,Guard.eval,Compare.eval,Operand32.eval,Operand64.eval,laneId,update,occurrence]

theorem output_accesses (cfg : Config n) (s : State n) (thread : Fin n)
    (block : (s.lanes thread).block = .output) (pc : (s.lanes thread).scalar.pc = 0)
    (live : (s.lanes thread).halted = false) (extent : n < s.global.length) :
    accesses (run cfg (List.replicate 2 thread) s).trace =
      [(.global,thread,⟨.store,bytePointer n,(s.lanes thread).scalar.regs 1⟩)] := by
  have fits : 4*n < 2^64 := by have := cfg.noWrap; omega
  have index : addressIndex s.global (bytePointer n) = .ok n := by
    simp [addressIndex,bytePointer,Nat.mod_eq_of_lt fits,extent]
  simp [accesses,memoryEvent,List.filterMap,run,runWith,List.replicate,step,dispatch,scalarStep,program,setLane,block,pc,live,
    eval,Instr.plain,Guard.eval,Operand32.eval,Operand64.eval,index,occurrence]

theorem leader_accesses (cfg : Config n) (s : State n) (thread : Fin n)
    (block : (s.lanes thread).block = .choose) (pc : (s.lanes thread).scalar.pc = 0)
    (live : (s.lanes thread).halted = false) (laneId : (s.lanes thread).scalar.regs 0 = 0)
    (globalExtent : n < s.global.length) (sharedExtent : n ≤ s.shared.length) :
    accesses (run cfg (List.replicate (6+(7*n+3)+2) thread) s).trace =
      loopAccesses s.shared thread 0 n ++ [(.global,thread,⟨.store,bytePointer n,total s.shared n⟩)] := by
  let initialized := (run cfg (List.replicate 6 thread) s).state
  obtain ⟨ib,ip,ic,ia,iad,il,ig,is,_,_⟩ := leader_initialize cfg s thread block pc live laneId
  change initialized.shared = s.shared at is
  change initialized.global = s.global at ig
  change (initialized.lanes thread).scalar.regs 1 = 0 at ia
  let summed := (run cfg (List.replicate (7*n+3) thread) initialized).state
  have fits : n < 2^32 := by have := cfg.noWrap; omega
  have pfits : 4*n < 2^64 := by have := cfg.noWrap; omega
  have bound : 0+n ≤ initialized.shared.length := by rw [is]; simpa using sharedExtent
  obtain ⟨sb,sp,sv,sl,sg,_,_,_⟩ := loop_execution cfg initialized thread ib ip il n 0 ic iad bound fits (by simpa using pfits)
  have sumValue : (summed.lanes thread).scalar.regs 1 = total s.shared n := by
    change (summed.lanes thread).scalar.regs 1 = Kernels.sliceSum initialized.shared 0 n ((initialized.lanes thread).scalar.regs 1) at sv
    simpa only [Kernels.sliceSum,List.drop_zero,ia,is,total] using sv
  change summed.global = initialized.global at sg
  rw [← List.replicate_append_replicate,run_append]
  change accesses ((run cfg (List.replicate (6+(7*n+3)) thread) s).trace ++
    (run cfg (List.replicate 2 thread) (run cfg (List.replicate (6+(7*n+3)) thread) s).state).trace) = _
  rw [accesses_append,← List.replicate_append_replicate,run_append]
  change accesses ((run cfg (List.replicate 6 thread) s).trace ++
    (run cfg (List.replicate (7*n+3) thread) initialized).trace) ++ accesses (run cfg (List.replicate 2 thread) summed).trace = _
  rw [accesses_append,initialize_no_accesses cfg s thread block pc live laneId,
    loop_accesses cfg initialized thread ib ip il n 0 ic iad bound fits (by simpa using pfits),
    output_accesses cfg summed thread sb sp sl (by rw [sg,ig]; exact globalExtent),sumValue,is]
  rfl



theorem followers_no_accesses (cfg : Config n) (s : State n) (lanes : List (Fin n))
    (distinct : lanes.Nodup)
    (ready : ∀ thread ∈ lanes, (s.lanes thread).block = .choose ∧
      (s.lanes thread).scalar.pc = 0 ∧ (s.lanes thread).halted = false ∧
      (s.lanes thread).scalar.regs 0 = BitVec.ofNat 32 thread.val ∧ thread.val ≠ 0) :
    accesses (run cfg (lanes.flatMap (List.replicate 3)) s).trace = [] := by
  induction lanes generalizing s with
  | nil => rfl
  | cons lane rest ih =>
    have unique := List.nodup_cons.mp distinct
    obtain ⟨b,p,l,r,nonzero⟩ := ready lane (by simp)
    obtain ⟨_,_,_,_,others⟩ := follower_exit cfg s lane b p l r nonzero
    let mid := (run cfg (List.replicate 3 lane) s).state
    have restReady : ∀ thread ∈ rest, (mid.lanes thread).block = .choose ∧
        (mid.lanes thread).scalar.pc = 0 ∧ (mid.lanes thread).halted = false ∧
        (mid.lanes thread).scalar.regs 0 = BitVec.ofNat 32 thread.val ∧ thread.val ≠ 0 := by
      intro thread member
      have different : thread ≠ lane := by intro h; subst thread; exact unique.1 member
      rw [show mid.lanes thread = s.lanes thread from others thread different]
      exact ready thread (by simp [member])
    have tail := ih mid unique.2 restReady
    rw [List.flatMap_cons,run_append]
    change accesses ((run cfg (List.replicate 3 lane) s).trace ++
      (run cfg (rest.flatMap (List.replicate 3)) mid).trace) = []
    rw [accesses_append,follower_no_accesses cfg s lane b p l r nonzero,tail]
    rfl

/-- Complete no-omission/no-invention memory trace for the actual whole program.
Dynamic occurrence indices remain in the original full trace; this projection
keeps their order and retains every actual memory effect. -/
theorem full_accesses (cfg : Config n) (input scratch : List Word) (seeds : Fin n → Seed)
    (inputs : n < input.length) (storage : n ≤ scratch.length) :
    accesses (run cfg (fullSchedule cfg) (start input scratch seeds)).trace =
      (List.finRange n).flatMap (producerAccesses input) ++
      loopAccesses input ⟨0,cfg.nonempty⟩ 0 n ++
      [(.global,⟨0,cfg.nonempty⟩,⟨.store,bytePointer n,total input n⟩)] := by
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
  obtain ⟨eg,es,_,_,eo⟩ := followers_phase cfg released (followers n) distinct ready
  let leader : Fin n := ⟨0,cfg.nonempty⟩
  have absent : leader ∉ followers n := by simp [followers,leader]
  have untouched : exited.lanes leader = released.lanes leader := eo leader absent
  have leaderReady : (exited.lanes leader).block = .choose ∧
      (exited.lanes leader).scalar.pc = 0 ∧ (exited.lanes leader).halted = false ∧
      (exited.lanes leader).scalar.regs 0 = 0 := by
    rw [untouched]; exact ⟨rfl,rfl,(pr leader).2.2.2,(pr leader).2.2.1⟩
  have sumEq : total exited.shared n = total input n := by
    rw [es,releasedShared]
    simp [total,List.length_take,Nat.min_eq_left (by omega : n ≤ input.length)]
  have readEq : loopAccesses exited.shared leader 0 n = loopAccesses input leader 0 n := by
    rw [es,releasedShared]
    apply List.map_congr_left
    intro i member
    have bound : i < n := List.mem_range.mp member
    simp [List.getElem!_eq_getElem?_getD,List.getElem?_append,List.length_take,
      Nat.min_eq_left (by omega : n ≤ input.length),bound,show i < input.length by omega]
  have leaderTrace := leader_accesses cfg exited leader leaderReady.1 leaderReady.2.1
    leaderReady.2.2.1 leaderReady.2.2.2 (by rw [eg,releasedGlobal]; exact inputs)
    (by rw [es,releasedShared]; simp only [List.length_append,List.length_take,List.length_drop]; omega)
  simp only [fullSchedule,run_append,accesses_append]
  rw [barrierEq]
  change accesses (run cfg (producerSchedule (List.finRange n)) initial).trace ++
    accesses (run cfg (SharedBarrier.schedule n) produced).trace ++
    accesses (run cfg ((followers n).flatMap (List.replicate 3)) released).trace ++
    accesses (run cfg (List.replicate (6+(7*n+3)+2) leader) exited).trace = _
  rw [producer_list_accesses cfg initial seeds (List.finRange n) (List.nodup_finRange n)
    (fun _ _ => rfl) (by change n ≤ input.length; omega) storage,
    barrier_round_accesses cfg produced pr pbar,followers_no_accesses cfg released (followers n) distinct ready,
    leaderTrace,sumEq,readEq]
  simp only [List.append_nil,List.append_assoc]
  rfl

end Ptx.Scalar.SharedReduction.Machine

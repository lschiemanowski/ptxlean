import Ptx.SharedReductionMemoryExistence
import Ptx.SharedReductionHistory
import Ptx.SharedReductionValues

/-! Actual-history source forcing for unrestricted candidate schedules. -/
namespace Ptx.Scalar.SharedReduction.Machine.Memory

/-- At-most-once is occurrence uniqueness, including equal repeated event values. -/
theorem count_at_most_one_position (trace : List α) (predicate : α → Bool)
    (once : trace.countP predicate ≤ 1) (i j : Nat) (a b : α)
    (atI : trace[i]? = some a) (atJ : trace[j]? = some b)
    (yesA : predicate a = true) (yesB : predicate b = true) : i = j := by
  induction trace generalizing i j with
  | nil => simp at atI
  | cons head tail ih =>
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero,Option.some.injEq] at atI
      subst head
      cases j with
      | zero => rfl
      | succ j =>
        have positive : 0 < tail.countP predicate :=
          List.countP_pos_iff.mpr ⟨b,List.mem_of_getElem? atJ,yesB⟩
        simp only [List.countP_cons,yesA,ite_true] at once
        omega
    | succ i =>
      cases j with
      | zero =>
        simp only [List.getElem?_cons_zero,Option.some.injEq] at atJ
        subst head
        have positive : 0 < tail.countP predicate :=
          List.countP_pos_iff.mpr ⟨a,List.mem_of_getElem? atI,yesA⟩
        simp only [List.countP_cons,yesB,ite_true] at once
        omega
      | succ j =>
        have bound : tail.countP predicate ≤ 1 := by
          simp only [List.countP_cons] at once
          split at once <;> omega
        exact congrArg Nat.succ (ih bound i j atI atJ)

/-- A subsequence is embedded at strictly increasing positions in the original
full trace. No injectivity of event values or uniqueness of PCs is required. -/
theorem sublist_positions (small large : List α) (sublist : small.Sublist large) :
    ∃ positions : Fin small.length → Nat,
      (∀ i, large[positions i]? = some small[i]) ∧
      (∀ i j, i.val < j.val → positions i < positions j) := by
  induction sublist with
  | slnil => exact ⟨Fin.elim0,fun i => Fin.elim0 i,fun i => Fin.elim0 i⟩
  | @cons small large a sub ih =>
    obtain ⟨positions,atPosition,increasing⟩ := ih
    exact ⟨fun i => positions i+1,fun i => atPosition i,fun i j lt => Nat.add_lt_add_right (increasing i j lt) 1⟩
  | @cons_cons small large a sub ih =>
    obtain ⟨positions,atPosition,increasing⟩ := ih
    let more : Fin (a::small).length → Nat := fun i =>
      if h : i.val = 0 then 0 else positions ⟨i.val-1,by have := i.isLt; simp only [List.length_cons] at this; omega⟩ + 1
    refine ⟨more,?_,?_⟩
    · intro i
      by_cases zero : i.val = 0
      · simp only [more,dite_eq_left zero,List.getElem?_cons_zero]
        change some a = some ((a::small)[i.val]'i.isLt)
        rw [List.getElem_cons]
        simp only [dite_eq_left zero]
      · have hi : i.val = (i.val-1)+1 := by omega
        simp only [more,dite_eq_right zero]
        rw [show (a::small)[i] = small[i.val-1]'(by have := i.isLt; simp only [List.length_cons] at this; omega) by
          change (a::small)[i.val]'i.isLt = _
          rw [List.getElem_cons]
          simp only [dite_eq_right zero]]
        exact atPosition _
    · intro i j lt
      by_cases iz : i.val = 0
      · have jz : j.val ≠ 0 := by omega
        simp only [more,dite_eq_left iz,dite_eq_right jz]
        omega
      · have jz : j.val ≠ 0 := by omega
        simp only [more,dite_eq_right iz,dite_eq_right jz]
        exact Nat.add_lt_add_right (increasing _ _ (by simp; omega)) 1

/-- Every actual indexed memory effect has its exact label in the execution graph. -/
theorem run_graph_complete (cfg : Config n) (reads : Nat → Option Word)
    (schedule : List (Fin n)) (s : State n) (position : Nat)
    (thread : Fin n) (block : Machine.Block) (space : Space)
    (occ : Scalar.Occurrence) (effect : MemoryEffect)
    (atIndex : (runWith cfg reads schedule s).trace[position]? = some (.scalar thread block (some space) occ))
    (memory : occ.memory = some effect) (source co) :
    ∃ r : Fin (runLabels cfg reads schedule s).length,
      (runGraph cfg reads schedule s source co).event r =
        ⟨some thread.val,position,(ofEffect space effect).effect⟩ := by
  obtain ⟨actualSpace,spaceEq,emitted⟩ := run_access_complete cfg reads schedule s thread block
    (some space) occ effect (List.mem_of_getElem? atIndex) memory
  have spaceSame := Option.some.inj spaceEq
  subst actualSpace
  have member : (⟨some thread.val,position,(ofEffect space effect).effect⟩ : Ptx.Occurrence) ∈
      runLabels cfg reads schedule s := by
    apply (TraceMemory.events_member_iff _ _ _ _ _).mpr
    exact .inr ⟨thread.val,List.mem_range.mpr thread.isLt,
      ⟨position,.scalar thread block (some space) occ,ofEffect space effect⟩,atIndex,emitted,rfl⟩
  obtain ⟨r,bound,label⟩ := List.mem_iff_getElem.mp member
  exact ⟨⟨r,bound⟩,label⟩

/-- Source constraints applied directly to an actual global-load effect. The
address equality is a structural instruction/address obligation, not freshness. -/
theorem run_global_load_value (cfg : Config n) (reads : Nat → Option Word)
    (schedule : List (Fin n)) (s : State n) (position : Nat)
    (thread : Fin n) (block : Machine.Block) (occ : Scalar.Occurrence) (effect : MemoryEffect)
    (atIndex : (runWith cfg reads schedule s).trace[position]? = some (.scalar thread block (some .global) occ))
    (memory : occ.memory = some effect) (load : effect.kind = .load)
    (i : Nat) (inside : i < n) (address : effect.address = bytePointer i)
    (source co) (sources : (runGraph cfg reads schedule s source co).Sources) :
    i < s.global.length ∧ effect.value = s.global[i]! := by
  obtain ⟨r,label⟩ := run_graph_complete cfg reads schedule s position thread block .global occ effect atIndex memory source co
  have read : (runGraph cfg reads schedule s source co).read r := by
    simp [Graph.read,label,ofEffect,TraceMemory.Access.effect,TraceMemory.AccessKind.op,load]
  have pointer : ((runGraph cfg reads schedule s source co).event r).effect.address =
      (⟨0,i⟩ : TraceMemory.Location 2).code := by
    simp [label,ofEffect,TraceMemory.Access.effect,location,slot,address,bytePointer_word cfg i (Nat.le_of_lt inside)]
  have result := run_global_input_read cfg reads schedule s source co r sources read i inside pointer
  exact ⟨result.2.1,by simpa [label,ofEffect,TraceMemory.Access.effect] using result.2.2⟩

theorem triple_earlier_positions (trace earlier suffix : List α) (a b c : α) (position : Nat)
    (splitTrace : trace = earlier ++ suffix) (earlierBefore : earlier.length ≤ position)
    (path : [a,b,c].Sublist earlier) :
    ∃ i j k, trace[i]? = some a ∧ trace[j]? = some b ∧ trace[k]? = some c ∧
      i < j ∧ j < k ∧ k < position := by
  obtain ⟨positions,atPosition,increasing⟩ := sublist_positions [a,b,c] earlier path
  let i := positions ⟨0,by simp⟩
  let j := positions ⟨1,by simp⟩
  let k := positions ⟨2,by simp⟩
  have ai : earlier[i]? = some a := atPosition ⟨0,by simp⟩
  have bj : earlier[j]? = some b := atPosition ⟨1,by simp⟩
  have ck : earlier[k]? = some c := atPosition ⟨2,by simp⟩
  have ib := (List.getElem?_eq_some_iff.mp ai).1
  have jb := (List.getElem?_eq_some_iff.mp bj).1
  have kb := (List.getElem?_eq_some_iff.mp ck).1
  refine ⟨i,j,k,?_,?_,?_,increasing _ _ (by simp),increasing _ _ (by simp),by omega⟩
  · simpa [splitTrace,List.getElem?_append,ib] using ai
  · simpa [splitTrace,List.getElem?_append,jb] using bj
  · simpa [splitTrace,List.getElem?_append,kb] using ck

/-- An arbitrary actual shared-store word is tied to its issuer's slot, not to
an inferred ownership label. -/
theorem run_shared_write_slot (cfg : Config n) (reads : Nat → Option Word)
    (schedule : List (Fin n)) (input scratch : List Word) (seeds : Fin n → Seed)
    (source co) (v : Fin (runLabels cfg reads schedule (start input scratch seeds)).length)
    (write : (runGraph cfg reads schedule (start input scratch seeds) source co).write v)
    (noninitial : ¬(runGraph cfg reads schedule (start input scratch seeds) source co).initial v)
    (i : Nat) (inside : i < n)
    (address : ((runGraph cfg reads schedule (start input scratch seeds) source co).event v).effect.address =
      (⟨1,i⟩ : TraceMemory.Location 2).code) :
    ∃ position block occ effect,
      (runWith cfg reads schedule (start input scratch seeds)).trace[position]? =
        some (.scalar ⟨i,inside⟩ block (some .shared) occ) ∧
      occ.memory = some effect ∧ effect.kind = .store ∧
      (runGraph cfg reads schedule (start input scratch seeds) source co).event v =
        ⟨some i,position,(ofEffect .shared effect).effect⟩ := by
  obtain ⟨thread,position,block,space,occ,effect,atIndex,fetch,executed,memory,store,label⟩ :=
    program_write_origin input scratch _ source co v write noninitial
  change (runGraph cfg reads schedule (start input scratch seeds) source co).event v = _ at label
  have locations : location space effect.address = (⟨1,i⟩ : TraceMemory.Location 2) := by
    apply TraceMemory.Location.code_injective
    simpa [label,ofEffect,TraceMemory.Access.effect] using address
  cases space with
  | global =>
    have impossible := congrArg (fun l : TraceMemory.Location 2 => l.storage.val) locations
    simp [location,slot] at impossible
  | shared =>
    have pointer := Data.runWith_producer_address cfg reads schedule (start input scratch seeds)
      thread block .shared occ effect (Control.initial input scratch seeds) (Data.initial input scratch seeds)
      (List.mem_of_getElem? atIndex) memory (.inr ⟨rfl,store⟩)
    have issuer : thread.val = i := by
      have words := congrArg TraceMemory.Location.word locations
      simpa [location,pointer,bytePointer_word cfg thread.val (Nat.le_of_lt thread.isLt)] using words
    have threadEq : thread = (⟨i,inside⟩ : Fin n) := Fin.ext issuer
    subst thread
    exact ⟨position,block,occ,effect,atIndex,memory,store,label⟩

/-- Actual history forbids two graph writes to the same shared producer slot. -/
theorem run_shared_write_unique (cfg : Config n) (reads : Nat → Option Word)
    (schedule : List (Fin n)) (input scratch : List Word) (seeds : Fin n → Seed)
    (source co) (a b : Fin (runLabels cfg reads schedule (start input scratch seeds)).length)
    (wa : (runGraph cfg reads schedule (start input scratch seeds) source co).write a)
    (wb : (runGraph cfg reads schedule (start input scratch seeds) source co).write b)
    (na : ¬(runGraph cfg reads schedule (start input scratch seeds) source co).initial a)
    (nb : ¬(runGraph cfg reads schedule (start input scratch seeds) source co).initial b)
    (i : Nat) (inside : i < n)
    (aa : ((runGraph cfg reads schedule (start input scratch seeds) source co).event a).effect.address =
      (⟨1,i⟩ : TraceMemory.Location 2).code)
    (ab : ((runGraph cfg reads schedule (start input scratch seeds) source co).event b).effect.address =
      (⟨1,i⟩ : TraceMemory.Location 2).code) : a = b := by
  obtain ⟨pa,ba,oa,ea,ha,ma,ka,la⟩ := run_shared_write_slot cfg reads schedule input scratch seeds source co a wa na i inside aa
  obtain ⟨pb,bb,ob,eb,hb,mb,kb,lb⟩ := run_shared_write_slot cfg reads schedule input scratch seeds source co b wb nb i inside ab
  have once : ((runWith cfg reads schedule (start input scratch seeds)).trace.countP
      (History.isPublication ⟨i,inside⟩)) ≤ 1 := by
    simpa [History.publications,List.countP_eq_length_filter] using
      History.publication_at_most_once cfg reads schedule input scratch seeds ⟨i,inside⟩
  have positions := count_at_most_one_position _ _ once pa pb _ _ ha hb
    ((History.isPublication_iff _ _).mpr ⟨ba,oa,ea,rfl,ma,ka⟩)
    ((History.isPublication_iff _ _).mpr ⟨bb,ob,eb,rfl,mb,kb⟩)
  apply graph_identity_injective input scratch _ source co
  change TraceMemory.identity ((runGraph cfg reads schedule (start input scratch seeds) source co).event a) =
    TraceMemory.identity ((runGraph cfg reads schedule (start input scratch seeds) source co).event b)
  simp [TraceMemory.identity,la,lb,positions]

/-- Every chosen shared read position has an actual earlier store/arrival path
from every participant, with the reader's own arrival at the same completion. -/
theorem run_shared_store_before (cfg : Config n) (reads : Nat → Option Word)
    (schedule : List (Fin n)) (input scratch : List Word) (seeds : Fin n → Seed)
    (thread writer : Fin n) (block : Machine.Block) (occ : Scalar.Occurrence)
    (effect : MemoryEffect) (position : Nat)
    (atIndex : (runWith cfg reads schedule (start input scratch seeds)).trace[position]? =
      some (.scalar thread block (some .shared) occ))
    (memory : occ.memory = some effect) (load : effect.kind = .load) :
    ∃ (storePosition : Nat), ∃ (storeBlock : Machine.Block), ∃ (storeOcc : Scalar.Occurrence), ∃ (stored : MemoryEffect),
      (runWith cfg reads schedule (start input scratch seeds)).trace[storePosition]? =
        some (.scalar writer storeBlock (some .shared) storeOcc) ∧
      storeOcc.memory = some stored ∧ stored.kind = .store ∧
      barrierOrder (runWith cfg reads schedule (start input scratch seeds)).trace
        ⟨some writer.val,storePosition,(ofEffect .shared stored).effect⟩
        ⟨some thread.val,position,(ofEffect .shared effect).effect⟩ := by
  obtain ⟨earlier,suffix,traceEq,before,paths⟩ :=
    History.load_prefix_at_index cfg reads schedule input scratch seeds thread block occ effect position atIndex memory load
  obtain ⟨store,published,path⟩ := paths writer
  obtain ⟨sp,ia,done,hs,ha,hc,sa,ac,cl⟩ :=
    triple_earlier_positions _ earlier suffix store
      (.barrier (.arrival (History.phaseKey cfg) writer)) (.barrier (.completion (History.phaseKey cfg)))
      position traceEq before path
  obtain ⟨readerStore,readerPublished,readerPath⟩ := paths thread
  obtain ⟨rsp,ib,readerDone,hrs,hb,hrc,rsa,rac,rcl⟩ :=
    triple_earlier_positions _ earlier suffix readerStore
      (.barrier (.arrival (History.phaseKey cfg) thread)) (.barrier (.completion (History.phaseKey cfg)))
      position traceEq before readerPath
  have once : ((runWith cfg reads schedule (start input scratch seeds)).trace.countP History.isCompletion) ≤ 1 := by
    simpa [History.completions,List.countP_eq_length_filter] using
      History.completion_at_most_once cfg reads schedule input scratch seeds
  have sameCompletion := count_at_most_one_position _ _ once done readerDone _ _ hc hrc
    (by simp [History.isCompletion]) (by simp [History.isCompletion])
  obtain ⟨storeBlock,storeOcc,stored,storeEq,storedMemory,storedKind⟩ := (History.isPublication_iff writer store).mp published
  subst store
  refine ⟨sp,storeBlock,storeOcc,stored,hs,storedMemory,storedKind,?_⟩
  exact ⟨History.phaseKey cfg,writer,thread,ia,ib,done,rfl,rfl,ha,hb,hc,sa,ac,by omega,cl⟩

/-- Unique actual publication plus completed-barrier order forces the read source.
The result supplies its producing instruction effect; no fresh-value premise occurs. -/
theorem run_shared_source (cfg : Config n) (reads : Nat → Option Word)
    (schedule : List (Fin n)) (input scratch : List Word) (seeds : Fin n → Seed)
    (thread : Fin n) (block : Machine.Block) (occ : Scalar.Occurrence) (effect : MemoryEffect)
    (position : Nat)
    (atIndex : (runWith cfg reads schedule (start input scratch seeds)).trace[position]? =
      some (.scalar thread block (some .shared) occ))
    (memory : occ.memory = some effect) (load : effect.kind = .load)
    (i : Nat) (inside : i < n) (address : effect.address = bytePointer i)
    (source co)
    (valid : Graph.Ordered.Valid (runGraph cfg reads schedule (start input scratch seeds) source co)
      (extra input scratch (runWith cfg reads schedule (start input scratch seeds)).trace source co)) :
    ∃ (storePosition : Nat), ∃ (storeBlock : Machine.Block), ∃ (storeOcc : Scalar.Occurrence), ∃ (stored : MemoryEffect),
      (runWith cfg reads schedule (start input scratch seeds)).trace[storePosition]? =
        some (Event.scalar (⟨i,inside⟩ : Fin n) storeBlock (some .shared) storeOcc) ∧
      storeOcc.memory = some stored ∧ stored.kind = .store ∧ effect.value = stored.value := by
  obtain ⟨sp,sb,so,stored,atStore,storeMemory,storeKind,order⟩ :=
    run_shared_store_before cfg reads schedule input scratch seeds thread ⟨i,inside⟩ block occ effect position atIndex memory load
  obtain ⟨r,readLabel⟩ := run_graph_complete cfg reads schedule (start input scratch seeds) position thread block .shared occ effect atIndex memory source co
  obtain ⟨w,writeLabel⟩ := run_graph_complete cfg reads schedule (start input scratch seeds) sp ⟨i,inside⟩ sb .shared so stored atStore storeMemory source co
  have storeAddress := Data.runWith_producer_address cfg reads schedule (start input scratch seeds)
    ⟨i,inside⟩ sb .shared so stored (Control.initial input scratch seeds) (Data.initial input scratch seeds)
    (List.mem_of_getElem? atStore) storeMemory (.inr ⟨rfl,storeKind⟩)
  have write : (runGraph cfg reads schedule (start input scratch seeds) source co).write w := by
    simp [Graph.write,writeLabel,ofEffect,TraceMemory.Access.effect,TraceMemory.AccessKind.op,storeKind]
  have read : (runGraph cfg reads schedule (start input scratch seeds) source co).read r := by
    simp [Graph.read,readLabel,ofEffect,TraceMemory.Access.effect,TraceMemory.AccessKind.op,load]
  have noninitial : ¬(runGraph cfg reads schedule (start input scratch seeds) source co).initial w := by
    simp [Graph.initial,writeLabel,ofEffect,TraceMemory.Access.effect,TraceMemory.AccessKind.op,storeKind]
  have readAddress : ((runGraph cfg reads schedule (start input scratch seeds) source co).event r).effect.address =
      (⟨1,i⟩ : TraceMemory.Location 2).code := by
    simp [readLabel,ofEffect,TraceMemory.Access.effect,location,slot,address,bytePointer_word cfg i (Nat.le_of_lt inside)]
  have writeAddress : ((runGraph cfg reads schedule (start input scratch seeds) source co).event w).effect.address =
      (⟨1,i⟩ : TraceMemory.Location 2).code := by
    simp [writeLabel,ofEffect,TraceMemory.Access.effect,location,slot,storeAddress,bytePointer_word cfg i (Nat.le_of_lt inside)]
  have same : (runGraph cfg reads schedule (start input scratch seeds) source co).sameAddress w r :=
    writeAddress.trans readAddress.symm
  have extraOrder : extra input scratch (runWith cfg reads schedule (start input scratch seeds)).trace source co w r := by
    change barrierOrder _ ((runGraph cfg reads schedule (start input scratch seeds) source co).event w)
      ((runGraph cfg reads schedule (start input scratch seeds) source co).event r)
    simpa [writeLabel,readLabel] using order
  have forced := barrier_unique_source input scratch _ source co w r valid write read same extraOrder
    (by
      intro v written notInitial atRead
      apply run_shared_write_unique cfg reads schedule input scratch seeds source co v w written write notInitial noninitial i inside
        (atRead.trans readAddress) writeAddress)
  refine ⟨sp,sb,so,stored,atStore,storeMemory,storeKind,?_⟩
  have values := forced.2
  change ((runGraph cfg reads schedule (start input scratch seeds) source co).event r).effect.value =
    ((runGraph cfg reads schedule (start input scratch seeds) source co).event w).effect.value at values
  simpa [readLabel,writeLabel,ofEffect,TraceMemory.Access.effect] using values

/-- Every admitted actual shared read observes its input word. Its unique store,
completed-barrier order, actual supplying global load and initialized value are
all derived; there is no assumption about the result or observed fresh value. -/
theorem run_shared_load_value (cfg : Config n) (reads : Nat → Option Word)
    (schedule : List (Fin n)) (input scratch : List Word) (seeds : Fin n → Seed)
    (position : Nat) (thread : Fin n) (block : Machine.Block)
    (occ : Scalar.Occurrence) (effect : MemoryEffect)
    (atIndex : (runWith cfg reads schedule (start input scratch seeds)).trace[position]? =
      some (.scalar thread block (some .shared) occ))
    (memory : occ.memory = some effect) (load : effect.kind = .load)
    (i : Nat) (inside : i < n) (address : effect.address = bytePointer i)
    (source co)
    (valid : Graph.Ordered.Valid (runGraph cfg reads schedule (start input scratch seeds) source co)
      (extra input scratch (runWith cfg reads schedule (start input scratch seeds)).trace source co)) :
    i < input.length ∧ effect.value = input[i]! := by
  obtain ⟨sp,sb,so,stored,atStore,storeMemory,storeKind,value⟩ :=
    run_shared_source cfg reads schedule input scratch seeds thread block occ effect position atIndex memory load
      i inside address source co valid
  have recorded := Data.runWith_shared_store_recorded cfg reads schedule (start input scratch seeds) []
    ⟨i,inside⟩ sb so stored (Control.initial input scratch seeds) (Data.value_initial input scratch seeds)
    (List.mem_of_getElem? atStore) storeMemory storeKind
  simp only [List.nil_append] at recorded
  obtain ⟨producerOcc,producerAddress,member,producerMemory⟩ := recorded
  have pointer := Data.runWith_producer_address cfg reads schedule (start input scratch seeds)
    ⟨i,inside⟩ .producer .global producerOcc ⟨.load,producerAddress,stored.value⟩
    (Control.initial input scratch seeds) (Data.initial input scratch seeds) member producerMemory (.inl ⟨rfl,rfl⟩)
  obtain ⟨pp,pbound,pat⟩ := List.mem_iff_getElem.mp member
  have inputValue := run_global_load_value cfg reads schedule (start input scratch seeds) pp
    ⟨i,inside⟩ .producer producerOcc ⟨.load,producerAddress,stored.value⟩
    (List.getElem?_eq_some_iff.mpr ⟨pbound,pat⟩) producerMemory rfl i inside pointer source co valid.sources
  exact ⟨inputValue.1,value.trans inputValue.2⟩

/-- Membership-facing form for execution invariants; the exact position is
recovered from the actual trace, not supplied as an occurrence-identity premise. -/
theorem run_shared_load_member_value (cfg : Config n) (reads : Nat → Option Word)
    (schedule : List (Fin n)) (input scratch : List Word) (seeds : Fin n → Seed)
    (thread : Fin n) (block : Machine.Block) (occ : Scalar.Occurrence) (effect : MemoryEffect)
    (member : .scalar thread block (some .shared) occ ∈
      (runWith cfg reads schedule (start input scratch seeds)).trace)
    (memory : occ.memory = some effect) (load : effect.kind = .load)
    (i : Nat) (inside : i < n) (address : effect.address = bytePointer i)
    (source co)
    (valid : Graph.Ordered.Valid (runGraph cfg reads schedule (start input scratch seeds) source co)
      (extra input scratch (runWith cfg reads schedule (start input scratch seeds)).trace source co)) :
    effect.value = input[i]! := by
  obtain ⟨position,bound,atPosition⟩ := List.mem_iff_getElem.mp member
  exact (run_shared_load_value cfg reads schedule input scratch seeds position thread block occ effect
    (List.getElem?_eq_some_iff.mpr ⟨bound,atPosition⟩) memory load i inside address source co valid).2

end Ptx.Scalar.SharedReduction.Machine.Memory

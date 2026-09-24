import Ptx.SharedReductionMemoryWitness
import Ptx.SharedReductionTrace

/-! Canonical execution facts used to discharge the separate existence witness.
The universal candidate theorem does not restrict candidates to this schedule. -/
namespace Ptx.Scalar.SharedReduction.Machine.Memory

open Ptx.TraceMemory

def canonicalTrace (cfg : Config n) (input scratch : List Word) (seeds : Fin n → Seed) : List (Event n) :=
  (run cfg (fullSchedule cfg) (start input scratch seeds)).trace

/-- The actual canonical accesses are strictly ordered by this phase/slot rank. -/
def accessRank (n : Nat) (a : Machine.Access n) : Nat :=
  let word := a.2.2.address.toNat / 4
  match a.1,a.2.2.kind with
  | .global,.load => 2*word
  | .shared,.store => 2*word+1
  | .shared,.load => 2*n+word
  | .global,.store => 3*n

theorem bytePointer_word (cfg : Config n) (i : Nat) (bound : i ≤ n) :
    (bytePointer i).toNat / 4 = i := by
  have fits : 4*i < 2^64 := by have := cfg.noWrap; omega
  simp [bytePointer,Nat.mod_eq_of_lt fits]

/-- Real canonical memory events have distinct chronological phase/slot ranks. -/
theorem canonical_accesses_ordered (cfg : Config n) (input scratch : List Word)
    (seeds : Fin n → Seed) (inputs : n < input.length) (storage : n ≤ scratch.length) :
    (accesses (canonicalTrace cfg input scratch seeds)).Pairwise
      (fun a b => accessRank n a < accessRank n b) := by
  rw [canonicalTrace,full_accesses cfg input scratch seeds inputs storage]
  rw [List.pairwise_append,List.pairwise_append]
  refine ⟨⟨?_,?_,?_⟩,?_,?_⟩
  · apply List.pairwise_flatMap.mpr
    constructor
    · intro thread member
      simp [producerAccesses,accessRank,bytePointer_word cfg thread.val (Nat.le_of_lt thread.isLt)]
    · apply List.pairwise_iff_getElem.mpr
      intro i j hi hj lt
      simp only [List.length_finRange] at hi hj
      simp only [List.getElem_finRange]
      intro a ha b hb
      simp only [producerAccesses,List.mem_cons,List.not_mem_nil,or_false] at ha hb
      rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;>
        simp [accessRank,bytePointer_word cfg i (Nat.le_of_lt hi),bytePointer_word cfg j (Nat.le_of_lt hj)] <;> omega
  · apply List.pairwise_iff_getElem.mpr
    intro i j hi hj lt
    simp only [loopAccesses,List.length_map,List.length_range] at hi hj
    simpa [loopAccesses,accessRank,bytePointer_word cfg i (Nat.le_of_lt hi),
      bytePointer_word cfg j (Nat.le_of_lt hj)] using lt
  · intro a ha b hb
    obtain ⟨thread,_,ha⟩ := List.mem_flatMap.mp ha
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hb
    have ib := List.mem_range.mp hi
    simp only [producerAccesses,List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl <;>
      simp [accessRank,bytePointer_word cfg thread.val (Nat.le_of_lt thread.isLt),
        bytePointer_word cfg i (Nat.le_of_lt ib)] <;> have := thread.isLt <;> omega
  · simp
  · intro a ha b hb
    simp only [List.mem_singleton] at hb
    subst b
    rcases List.mem_append.mp ha with producer | loop
    · obtain ⟨thread,_,ha⟩ := List.mem_flatMap.mp producer
      simp only [producerAccesses,List.mem_cons,List.not_mem_nil,or_false] at ha
      rcases ha with rfl | rfl <;>
        simp [accessRank,bytePointer_word cfg thread.val (Nat.le_of_lt thread.isLt)] <;>
        have := thread.isLt <;> omega
    · obtain ⟨i,hi,rfl⟩ := List.mem_map.mp loop
      have ib := List.mem_range.mp hi
      simp [accessRank,bytePointer_word cfg i (Nat.le_of_lt ib)]
      omega

/-- Raw memory filtering and the checked adapter agree on every actual event. -/
theorem run_access_iff_raw (cfg : Config n) (reads : Nat → Option Word)
    (schedule : List (Fin n)) (s : State n) (event : Event n)
    (member : event ∈ (runWith cfg reads schedule s).trace) (t : Nat) (a : TraceMemory.Access 2) :
    access t event = some a ↔ ∃ space, ∃ (thread : Fin n), ∃ effect,
      memoryEvent event = some (space,thread,effect) ∧ thread.val = t ∧ a = ofEffect space effect := by
  constructor
  · intro emitted
    obtain ⟨thread,block,space,occ,effect,rfl,threadEq,_,_,memory,_,rfl⟩ := access_origin t event a emitted
    exact ⟨space,thread,effect,by simp [memoryEvent,memory],threadEq,rfl⟩
  · rintro ⟨space,thread,effect,raw,threadEq,rfl⟩
    cases event with
    | scalar et block es occ =>
      cases es with
      | none => simp [memoryEvent] at raw
      | some actualSpace =>
        cases hm : occ.memory with
        | none => simp [memoryEvent,hm] at raw
        | some actualEffect =>
          simp only [memoryEvent,hm,Option.map_some,Option.some.injEq,Prod.mk.injEq] at raw
          obtain ⟨rfl,rfl,rfl⟩ := raw
          obtain ⟨space,spaceEq,emitted⟩ := run_access_complete cfg reads schedule s et block
            (some actualSpace) occ actualEffect member hm
          have sameSpace := Option.some.inj spaceEq
          simpa [threadEq,← sameSpace] using emitted
    | branch => simp [memoryEvent] at raw
    | barrier => simp [memoryEvent] at raw
    | exit => simp [memoryEvent] at raw

theorem canonical_rank_increases (cfg : Config n) (input scratch : List Word)
    (seeds : Fin n → Seed) (inputs : n < input.length) (storage : n ≤ scratch.length)
    (i j : Nat) (ei ej : Event n) (ai aj : Machine.Access n)
    (hi : (canonicalTrace cfg input scratch seeds)[i]? = some ei)
    (hj : (canonicalTrace cfg input scratch seeds)[j]? = some ej)
    (mi : memoryEvent ei = some ai) (mj : memoryEvent ej = some aj) (before : i < j) :
    accessRank n ai < accessRank n aj := by
  have pairwise := List.pairwise_filterMap.mp (canonical_accesses_ordered cfg input scratch seeds inputs storage)
  obtain ⟨ib,ie⟩ := List.getElem?_eq_some_iff.mp hi
  obtain ⟨jb,je⟩ := List.getElem?_eq_some_iff.mp hj
  exact List.pairwise_iff_getElem.mp pairwise i j ib jb before ai (ie ▸ mi) aj (je ▸ mj)

/-- Rank of the same dynamic access after space/word encoding. -/
def effectRank (n : Nat) (effect : Effect) : Nat :=
  let word := effect.address / 2
  match effect.op with
  | .load _ => if effect.address % 2 = 0 then 2*word else 2*n+word
  | .store _ => if effect.address % 2 = 0 then 3*n else 2*word+1
  | .init => 0

theorem effect_rank_recover (space : Space) (thread : Fin n) (effect : MemoryEffect) :
    effectRank n (ofEffect space effect).effect = accessRank n (space,thread,effect) := by
  cases space <;> cases hk : effect.kind <;>
    simp [effectRank,ofEffect,Access.effect,AccessKind.op,location,slot,Location.code,accessRank,hk] <;> omega

theorem canonical_program_origin (cfg : Config n) (input scratch : List Word)
    (seeds : Fin n → Seed) (source co)
    (w : Fin (labels input scratch (canonicalTrace cfg input scratch seeds)).length)
    (programEvent : ((graph input scratch (canonicalTrace cfg input scratch seeds) source co).event w).thread ≠ none) :
    ∃ position event space, ∃ (thread : Fin n), ∃ effect,
      (canonicalTrace cfg input scratch seeds)[position]? = some event ∧
      memoryEvent event = some (space,thread,effect) ∧
      (graph input scratch (canonicalTrace cfg input scratch seeds) source co).event w =
        ⟨some thread.val,position,(ofEffect space effect).effect⟩ := by
  have member : (graph input scratch (canonicalTrace cfg input scratch seeds) source co).event w
      ∈ labels input scratch (canonicalTrace cfg input scratch seeds) := List.getElem_mem _
  rcases labels_origin input scratch _ _ member with ⟨i,hi,he⟩ | ⟨t,ht,p,hp,ha,he⟩
  · exact False.elim (programEvent (by simp [← he,Initial.occurrence]))
  · obtain ⟨thread,block,space,occ,effect,origin,threadEq,_,_,memory,_,value⟩ := access_origin t p.origin p.access ha
    refine ⟨p.position,p.origin,space,thread,effect,hp,?_,?_⟩
    · simp [origin,memoryEvent,memory]
    · rw [← he]
      simp [Projected.occurrence,value,threadEq]

theorem canonical_program_rank (cfg : Config n) (input scratch : List Word)
    (seeds : Fin n → Seed) (inputs : n < input.length) (storage : n ≤ scratch.length)
    (source co) (a b : Fin (labels input scratch (canonicalTrace cfg input scratch seeds)).length)
    (pa : ((graph input scratch (canonicalTrace cfg input scratch seeds) source co).event a).thread ≠ none)
    (pb : ((graph input scratch (canonicalTrace cfg input scratch seeds) source co).event b).thread ≠ none)
    (before : ((graph input scratch (canonicalTrace cfg input scratch seeds) source co).event a).position <
      ((graph input scratch (canonicalTrace cfg input scratch seeds) source co).event b).position) :
    effectRank n ((graph input scratch (canonicalTrace cfg input scratch seeds) source co).event a).effect <
      effectRank n ((graph input scratch (canonicalTrace cfg input scratch seeds) source co).event b).effect := by
  obtain ⟨ia,ea,sa,ta,ma,ha,ra,la⟩ := canonical_program_origin cfg input scratch seeds source co a pa
  obtain ⟨ib,eb,sb,tb,mb,hb,rb,lb⟩ := canonical_program_origin cfg input scratch seeds source co b pb
  have lt : ia < ib := by simpa [la,lb] using before
  have result := canonical_rank_increases cfg input scratch seeds inputs storage ia ib ea eb
    (sa,ta,ma) (sb,tb,mb) ha hb ra rb lt
  rw [la,lb]
  change effectRank n (ofEffect sa ma).effect < effectRank n (ofEffect sb mb).effect
  rw [effect_rank_recover sa ta ma,effect_rank_recover sb tb mb]
  exact result

theorem canonical_memory_classification (cfg : Config n) (input scratch : List Word)
    (seeds : Fin n → Seed) (inputs : n < input.length) (storage : n ≤ scratch.length)
    (a : Machine.Access n) (member : a ∈ accesses (canonicalTrace cfg input scratch seeds)) :
    (∃ t : Fin n, a = (.global,t,⟨.load,bytePointer t.val,input[t.val]!⟩)) ∨
    (∃ t : Fin n, a = (.shared,t,⟨.store,bytePointer t.val,input[t.val]!⟩)) ∨
    (∃ i, i < n ∧ a = (.shared,⟨0,cfg.nonempty⟩,⟨.load,bytePointer i,input[i]!⟩)) ∨
    a = (.global,⟨0,cfg.nonempty⟩,⟨.store,bytePointer n,total input n⟩) := by
  rw [canonicalTrace,full_accesses cfg input scratch seeds inputs storage] at member
  rcases List.mem_append.mp member with before | output
  · rcases List.mem_append.mp before with producer | loop
    · obtain ⟨t,_,atThread⟩ := List.mem_flatMap.mp producer
      simp only [producerAccesses,List.mem_cons,List.not_mem_nil,or_false] at atThread
      rcases atThread with h | h
      · exact .inl ⟨t,h⟩
      · exact .inr (.inl ⟨t,h⟩)
    · obtain ⟨i,hi,h⟩ := List.mem_map.mp loop
      exact .inr (.inr (.inl ⟨i,List.mem_range.mp hi,by simpa using h.symm⟩))
  · exact .inr (.inr (.inr (List.mem_singleton.mp output)))

/-- Completeness gives a graph index for every actual raw memory occurrence. -/
theorem canonical_access_exists (cfg : Config n) (input scratch : List Word)
    (seeds : Fin n → Seed) (source co) (space : Space) (thread : Fin n) (effect : MemoryEffect)
    (member : (space,thread,effect) ∈ accesses (canonicalTrace cfg input scratch seeds)) :
    ∃ w : Fin (labels input scratch (canonicalTrace cfg input scratch seeds)).length, ∃ position,
      (graph input scratch (canonicalTrace cfg input scratch seeds) source co).event w =
        ⟨some thread.val,position,(ofEffect space effect).effect⟩ := by
  obtain ⟨event,member,raw⟩ := List.mem_filterMap.mp member
  obtain ⟨position,bound,atPosition⟩ := List.mem_iff_getElem.mp member
  have emitted : access thread.val event = some (ofEffect space effect) :=
    (run_access_iff_raw cfg (fun _ => none) (fullSchedule cfg) (start input scratch seeds)
      event member thread.val (ofEffect space effect)).mpr ⟨space,thread,effect,raw,rfl,rfl⟩
  have p : (⟨position,event,ofEffect space effect⟩ : Projected 2 (Event n)) ∈
      projection thread.val (canonicalTrace cfg input scratch seeds) :=
    projection_complete _ _ _ _ _ (List.getElem?_eq_some_iff.mpr ⟨bound,atPosition⟩) emitted
  have labelMember : (⟨some thread.val,position,(ofEffect space effect).effect⟩ : Ptx.Occurrence) ∈
      labels input scratch (canonicalTrace cfg input scratch seeds) := by
    apply (events_member_iff _ _ _ _ _).mpr
    exact .inr ⟨thread.val,List.mem_range.mpr thread.isLt,⟨position,event,ofEffect space effect⟩,
      List.getElem?_eq_some_iff.mpr ⟨bound,atPosition⟩,emitted,rfl⟩
  obtain ⟨i,hi,he⟩ := List.mem_iff_getElem.mp labelMember
  exact ⟨⟨i,hi⟩,position,he⟩

def rankBase (global shared : List Word) : Nat := 2*(global.length+shared.length)+1

def eventRank (n : Nat) (global shared : List Word) (e : Ptx.Occurrence) : Nat :=
  match e.thread with
  | none => e.effect.address
  | some _ => rankBase global shared + effectRank n e.effect

theorem initial_rank_bound (global shared : List Word) (i : Initial 2)
    (member : i ∈ initial global shared) : i.location.code < rankBase global shared := by
  rcases List.mem_append.mp member with hg | hs
  · obtain ⟨j,hj,rfl⟩ := List.mem_mapIdx.mp hg
    simp only [Location.code,Fin.val_zero,rankBase]
    omega
  · obtain ⟨j,hj,rfl⟩ := List.mem_mapIdx.mp hs
    simp only [Location.code,rankBase]
    change 2*j+1 < 2*(global.length+shared.length)+1
    omega

theorem initial_event_origin (global shared : List Word) (trace : List (Event n))
    (source co) (w : Fin (labels global shared trace).length)
    (noneThread : ((graph global shared trace source co).event w).thread = none) :
    ∃ i ∈ initial global shared, (graph global shared trace source co).event w = i.occurrence := by
  have member : (graph global shared trace source co).event w ∈ labels global shared trace := List.getElem_mem _
  rcases labels_origin global shared trace _ member with ⟨i,hi,he⟩ | ⟨t,ht,p,hp,ha,he⟩
  · exact ⟨i,hi,he.symm⟩
  · simp [← he,Projected.occurrence] at noneThread

theorem graph_identity_injective (global shared : List Word) (trace : List (Event n))
    (source co) : Function.Injective (fun w : Fin (labels global shared trace).length =>
      identity ((graph global shared trace source co).event w)) := by
  intro a b equal
  apply Fin.ext
  have unique := labels_unique global shared trace
  apply unique.eq_of_getElem_eq (by simp) (by simp)
  simpa [graph,TraceMemory.graph] using equal

theorem canonical_position_injective (cfg : Config n) (input scratch : List Word)
    (seeds : Fin n → Seed) (source co)
    (a b : Fin (labels input scratch (canonicalTrace cfg input scratch seeds)).length)
    (pa : ((graph input scratch (canonicalTrace cfg input scratch seeds) source co).event a).thread ≠ none)
    (pb : ((graph input scratch (canonicalTrace cfg input scratch seeds) source co).event b).thread ≠ none)
    (position : ((graph input scratch (canonicalTrace cfg input scratch seeds) source co).event a).position =
      ((graph input scratch (canonicalTrace cfg input scratch seeds) source co).event b).position) : a = b := by
  obtain ⟨ia,ea,sa,ta,ma,ha,ra,la⟩ := canonical_program_origin cfg input scratch seeds source co a pa
  obtain ⟨ib,eb,sb,tb,mb,hb,rb,lb⟩ := canonical_program_origin cfg input scratch seeds source co b pb
  have indices : ia = ib := by simpa [la,lb] using position
  have events : ea = eb := Option.some.inj (ha.symm.trans (indices ▸ hb))
  have raw : (sa,ta,ma) = (sb,tb,mb) := Option.some.inj (ra.symm.trans (events ▸ rb))
  have threads : ta = tb := congrArg (fun x : Machine.Access n => x.2.1) raw
  apply graph_identity_injective input scratch _ source co
  simp [identity,la,lb,threads,indices]

theorem canonical_rank_injective (cfg : Config n) (input scratch : List Word)
    (seeds : Fin n → Seed) (inputs : n < input.length) (storage : n ≤ scratch.length)
    (source co) : Function.Injective (fun w : Fin (labels input scratch (canonicalTrace cfg input scratch seeds)).length =>
      eventRank n input scratch ((graph input scratch (canonicalTrace cfg input scratch seeds) source co).event w)) := by
  intro a b same
  let g := graph input scratch (canonicalTrace cfg input scratch seeds) source co
  change eventRank n input scratch (g.event a) = eventRank n input scratch (g.event b) at same
  by_cases pa : (g.event a).thread = none
  · obtain ⟨ia,ha,la⟩ := initial_event_origin input scratch _ source co a pa
    change g.event a = ia.occurrence at la
    by_cases pb : (g.event b).thread = none
    · obtain ⟨ib,hb,lb⟩ := initial_event_origin input scratch _ source co b pb
      change g.event b = ib.occurrence at lb
      have addresses : ia.location.code = ib.location.code := by simpa [eventRank,la,lb,Initial.occurrence] using same
      apply graph_identity_injective input scratch _ source co
      change identity (g.event a) = identity (g.event b)
      simp [identity,la,lb,Initial.occurrence,addresses]
    · have bound := initial_rank_bound input scratch ia ha
      cases ht : (g.event b).thread with
      | none => exact False.elim (pb ht)
      | some t =>
        have eq : ia.location.code = rankBase input scratch + effectRank n (g.event b).effect := by
          simpa [eventRank,la,Initial.occurrence,ht] using same
        omega
  · by_cases pb : (g.event b).thread = none
    · obtain ⟨ib,hb,lb⟩ := initial_event_origin input scratch _ source co b pb
      change g.event b = ib.occurrence at lb
      have bound := initial_rank_bound input scratch ib hb
      cases ht : (g.event a).thread with
      | none => exact False.elim (pa ht)
      | some t =>
        have eq : rankBase input scratch + effectRank n (g.event a).effect = ib.location.code := by
          simpa [eventRank,lb,Initial.occurrence,ht] using same
        omega
    · have rankEq : effectRank n (g.event a).effect = effectRank n (g.event b).effect := by
        cases ha : (g.event a).thread <;> cases hb : (g.event b).thread <;> simp_all [eventRank]
      have position : (g.event a).position = (g.event b).position := by
        rcases Nat.lt_trichotomy (g.event a).position (g.event b).position with lt | eq | gt
        · have h := canonical_program_rank cfg input scratch seeds inputs storage source co a b pa pb lt
          change effectRank n (g.event a).effect < effectRank n (g.event b).effect at h
          omega
        · exact eq
        · have h := canonical_program_rank cfg input scratch seeds inputs storage source co b a pb pa gt
          change effectRank n (g.event b).effect < effectRank n (g.event a).effect at h
          omega
      exact canonical_position_injective cfg input scratch seeds source co a b pa pb position

theorem graph_initial_iff (global shared : List Word) (trace : List (Event n))
    (source co) (w : Fin (labels global shared trace).length) :
    (graph global shared trace source co).initial w ↔
      ((graph global shared trace source co).event w).thread = none := by
  constructor
  · intro init
    have member : (graph global shared trace source co).event w ∈ labels global shared trace := List.getElem_mem _
    rcases labels_origin global shared trace _ member with ⟨i,hi,he⟩ | ⟨t,ht,p,hp,ha,he⟩
    · simp [← he,Initial.occurrence]
    · have impossible : p.access.kind.op = .init := by
        simpa [Graph.initial,← he,Projected.occurrence,TraceMemory.Access.effect] using init
      cases hk : p.access.kind <;> simp [AccessKind.op,hk] at impossible
  · intro noThread
    obtain ⟨i,hi,he⟩ := initial_event_origin global shared trace source co w noThread
    simp [Graph.initial,he,Initial.occurrence]

end Ptx.Scalar.SharedReduction.Machine.Memory

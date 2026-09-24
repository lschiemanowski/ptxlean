import Ptx.SharedReductionMemoryCanonical

namespace Ptx.Scalar.SharedReduction.Machine.Memory

open Ptx.TraceMemory

/-- Every supplied initial word has an actual graph index. -/
theorem initial_index (global shared : List Word) (trace : List (Event n))
    (source co) (i : Initial 2) (member : i ∈ initial global shared) :
    ∃ w : Fin (labels global shared trace).length,
      (graph global shared trace source co).event w = i.occurrence := by
  have labelMember : i.occurrence ∈ labels global shared trace := by
    apply (events_member_iff _ _ _ _ _).mpr
    exact .inl ⟨i,member,rfl⟩
  obtain ⟨w,bound,equal⟩ := List.mem_iff_getElem.mp labelMember
  exact ⟨⟨w,bound⟩,equal⟩

theorem initial_global_member (input scratch : List Word) (i : Nat) (bound : i < input.length) :
    (⟨⟨0,i⟩,input[i]!⟩ : Initial 2) ∈ initial input scratch := by
  apply List.mem_append_left
  apply List.mem_mapIdx.mpr
  exact ⟨i,bound,by simp [bound]⟩

/-- Only a producer's shared store or the final output store can be a program write. -/
theorem canonical_write (cfg : Config n) (input scratch : List Word) (seeds : Fin n → Seed)
    (inputs : n < input.length) (storage : n ≤ scratch.length) (source co)
    (w : Fin (labels input scratch (canonicalTrace cfg input scratch seeds)).length)
    (write : (graph input scratch (canonicalTrace cfg input scratch seeds) source co).write w)
    (notInitial : ¬(graph input scratch (canonicalTrace cfg input scratch seeds) source co).initial w) :
    ((∃ t : Fin n, ∃ position,
      (graph input scratch (canonicalTrace cfg input scratch seeds) source co).event w =
        ⟨some t.val,position,(ofEffect .shared ⟨.store,bytePointer t.val,input[t.val]!⟩).effect⟩)) ∨
    (∃ position, (graph input scratch (canonicalTrace cfg input scratch seeds) source co).event w =
      ⟨some 0,position,(ofEffect .global ⟨.store,bytePointer n,total input n⟩).effect⟩) := by
  obtain ⟨thread,position,block,space,occ,effect,atIndex,fetch,executed,memory,store,label⟩ :=
    program_write_origin input scratch _ source co w write notInitial
  have member : (space,thread,effect) ∈ accesses (canonicalTrace cfg input scratch seeds) :=
    List.mem_filterMap.mpr ⟨_,List.mem_of_getElem? atIndex,by simp [memoryEvent,memory]⟩
  rcases canonical_memory_classification cfg input scratch seeds inputs storage _ member with
    ⟨t,equal⟩ | ⟨t,equal⟩ | ⟨i,hi,equal⟩ | equal
  · have kindEq := congrArg (fun x : Machine.Access n => x.2.2.kind) equal
    simp [store] at kindEq
  · obtain ⟨rfl,tail⟩ := Prod.mk.inj equal
    obtain ⟨rfl,rfl⟩ := Prod.mk.inj tail
    exact .inl ⟨_,position,label⟩
  · have kindEq := congrArg (fun x : Machine.Access n => x.2.2.kind) equal
    simp [store] at kindEq
  · obtain ⟨rfl,tail⟩ := Prod.mk.inj equal
    obtain ⟨rfl,rfl⟩ := Prod.mk.inj tail
    exact .inr ⟨position,label⟩

theorem canonical_read (cfg : Config n) (input scratch : List Word) (seeds : Fin n → Seed)
    (inputs : n < input.length) (storage : n ≤ scratch.length) (source co)
    (r : Fin (labels input scratch (canonicalTrace cfg input scratch seeds)).length)
    (read : (graph input scratch (canonicalTrace cfg input scratch seeds) source co).read r) :
    (∃ t : Fin n, ∃ position,
      (graph input scratch (canonicalTrace cfg input scratch seeds) source co).event r =
        ⟨some t.val,position,(ofEffect .global ⟨.load,bytePointer t.val,input[t.val]!⟩).effect⟩) ∨
    (∃ i, i < n ∧ ∃ position,
      (graph input scratch (canonicalTrace cfg input scratch seeds) source co).event r =
        ⟨some 0,position,(ofEffect .shared ⟨.load,bytePointer i,input[i]!⟩).effect⟩) := by
  have notInitial : ¬(graph input scratch (canonicalTrace cfg input scratch seeds) source co).initial r := by
    intro initial
    change ((graph input scratch (canonicalTrace cfg input scratch seeds) source co).event r).effect.op = .init at initial
    simp [Graph.read,initial] at read
  have programEvent := mt (graph_initial_iff input scratch _ source co r).mpr notInitial
  obtain ⟨position,event,space,thread,effect,atIndex,raw,label⟩ :=
    canonical_program_origin cfg input scratch seeds source co r programEvent
  have member : (space,thread,effect) ∈ accesses (canonicalTrace cfg input scratch seeds) :=
    List.mem_filterMap.mpr ⟨event,List.mem_of_getElem? atIndex,raw⟩
  rcases canonical_memory_classification cfg input scratch seeds inputs storage _ member with
    ⟨t,equal⟩ | ⟨t,equal⟩ | ⟨i,hi,equal⟩ | equal
  all_goals
    obtain ⟨rfl,tail⟩ := Prod.mk.inj equal
    obtain ⟨rfl,rfl⟩ := Prod.mk.inj tail
  · exact .inl ⟨_,position,label⟩
  · simp [Graph.read,label,ofEffect,TraceMemory.Access.effect,AccessKind.op] at read
  · exact .inr ⟨i,hi,position,label⟩
  · simp [Graph.read,label,ofEffect,TraceMemory.Access.effect,AccessKind.op] at read

theorem ofEffect_pointer (cfg : Config n) (space : Space) (kind : MemoryKind)
    (i : Nat) (value : Word) (bound : i ≤ n) :
    ofEffect space ⟨kind,bytePointer i,value⟩ =
      ⟨⟨slot space,i⟩,(match kind with | .load => .load .relaxed | .store => .store .relaxed),value⟩ := by
  cases kind <;> simp [ofEffect,location,bytePointer_word cfg i bound]

theorem canonical_global_initial (cfg : Config n) (input scratch : List Word) (seeds : Fin n → Seed)
    (source co) (v : Fin (labels input scratch (canonicalTrace cfg input scratch seeds)).length)
    (write : (graph input scratch (canonicalTrace cfg input scratch seeds) source co).write v)
    (i : Nat) (inside : i < n)
    (address : ((graph input scratch (canonicalTrace cfg input scratch seeds) source co).event v).effect.address =
      (⟨0,i⟩ : Location 2).code) :
    (graph input scratch (canonicalTrace cfg input scratch seeds) source co).initial v := by
  by_cases initial : (graph input scratch (canonicalTrace cfg input scratch seeds) source co).initial v
  · exact initial
  · have output := program_global_write_address cfg (fun _ => none) (fullSchedule cfg)
      (start input scratch seeds) input scratch source co v write initial i address
    omega

theorem canonical_shared_latest (cfg : Config n) (input scratch : List Word) (seeds : Fin n → Seed)
    (inputs : n < input.length) (storage : n ≤ scratch.length) (source co)
    (v : Fin (labels input scratch (canonicalTrace cfg input scratch seeds)).length)
    (write : (graph input scratch (canonicalTrace cfg input scratch seeds) source co).write v)
    (i : Nat) (_inside : i < n)
    (address : ((graph input scratch (canonicalTrace cfg input scratch seeds) source co).event v).effect.address =
      (⟨1,i⟩ : Location 2).code) :
    eventRank n input scratch ((graph input scratch (canonicalTrace cfg input scratch seeds) source co).event v) ≤
      rankBase input scratch + (2*i+1) := by
  by_cases initial : (graph input scratch (canonicalTrace cfg input scratch seeds) source co).initial v
  · obtain ⟨iv,hv,lv⟩ := initial_event_origin input scratch _ source co v
      ((graph_initial_iff input scratch _ source co v).mp initial)
    have bound := initial_rank_bound input scratch iv hv
    simp only [lv,eventRank,Initial.occurrence]
    omega
  · rcases canonical_write cfg input scratch seeds inputs storage source co v write initial with
      ⟨t,position,label⟩ | ⟨position,label⟩
    · have same : t.val = i := by
        have eq := address
        simp [label,ofEffect_pointer cfg .shared .store t.val _ (Nat.le_of_lt t.isLt),
          TraceMemory.Access.effect,Location.code,slot] at eq
        omega
      simp [label,eventRank,ofEffect_pointer cfg .shared .store t.val _ (Nat.le_of_lt t.isLt),
        effectRank,TraceMemory.Access.effect,AccessKind.op,Location.code,slot]
      omega
    · have impossible : 2*n = 2*i+1 := by
        simpa [label,ofEffect_pointer cfg .global .store n _ (Nat.le_refl n),
          TraceMemory.Access.effect,Location.code,slot] using address
      omega

/-- Canonical actual reads each have a matching preceding source; every competing
write at that word has no greater rank. These are derived facts, not premises. -/
theorem canonical_source_exists (cfg : Config n) (input scratch : List Word) (seeds : Fin n → Seed)
    (inputs : n < input.length) (storage : n ≤ scratch.length) (source co)
    (r : Fin (labels input scratch (canonicalTrace cfg input scratch seeds)).length)
    (read : (graph input scratch (canonicalTrace cfg input scratch seeds) source co).read r) :
    let g := graph input scratch (canonicalTrace cfg input scratch seeds) source co
    let rank := fun w => eventRank n input scratch (g.event w)
    ∃ w, g.write w ∧ g.sameAddress w r ∧ (g.event w).effect.value = (g.event r).effect.value ∧
      rank w < rank r ∧ (∀ v, g.write v → g.sameAddress v r → rank v ≤ rank w) := by
  rcases canonical_read cfg input scratch seeds inputs storage source co r read with
    ⟨t,position,label⟩ | ⟨i,inside,position,label⟩
  · obtain ⟨w,initialLabel⟩ := initial_index input scratch (canonicalTrace cfg input scratch seeds) source co
      ⟨⟨0,t.val⟩,input[t.val]!⟩ (initial_global_member input scratch t.val (by have := t.isLt; omega))
    refine ⟨w,?_,?_,?_,?_,?_⟩
    · simp [Graph.write,initialLabel,Initial.occurrence]
    · simp [Graph.sameAddress,initialLabel,Initial.occurrence,label,
        ofEffect_pointer cfg .global .load t.val _ (Nat.le_of_lt t.isLt),TraceMemory.Access.effect,slot]
    · simp [initialLabel,label,Initial.occurrence,ofEffect,TraceMemory.Access.effect]
    · have bound := initial_rank_bound input scratch (⟨⟨0,t.val⟩,input[t.val]!⟩ : Initial 2)
        (initial_global_member input scratch t.val (by have := t.isLt; omega))
      simp only [initialLabel,Initial.occurrence,eventRank,label]
      exact Nat.lt_of_lt_of_le bound (Nat.le_add_right _ _)
    · intro v write same
      have address : ((graph input scratch (canonicalTrace cfg input scratch seeds) source co).event v).effect.address =
          (⟨0,t.val⟩ : Location 2).code := by
        simpa [Graph.sameAddress,label,ofEffect_pointer cfg .global .load t.val _ (Nat.le_of_lt t.isLt),
          TraceMemory.Access.effect,slot] using same
      have init := canonical_global_initial cfg input scratch seeds source co v write t.val t.isLt address
      have noneThread := (graph_initial_iff input scratch _ source co v).mp init
      simp [eventRank,noneThread,initialLabel,Initial.occurrence,address]
  · let t : Fin n := ⟨i,inside⟩
    have member : (.shared,t,⟨.store,bytePointer i,input[i]!⟩) ∈ accesses (canonicalTrace cfg input scratch seeds) := by
      rw [canonicalTrace,full_accesses cfg input scratch seeds inputs storage]
      apply List.mem_append_left
      apply List.mem_append_left
      apply List.mem_flatMap.mpr
      exact ⟨t,List.mem_finRange t,by simp [producerAccesses,t]⟩
    obtain ⟨w,wp,storeLabel⟩ := canonical_access_exists cfg input scratch seeds source co .shared t _ member
    have wrank : eventRank n input scratch ((graph input scratch (canonicalTrace cfg input scratch seeds) source co).event w) =
        rankBase input scratch + (2*i+1) := by
      simp [storeLabel,eventRank,ofEffect_pointer cfg .shared .store i _ (Nat.le_of_lt inside),
        TraceMemory.Access.effect,Location.code,slot,effectRank,AccessKind.op]
      omega
    refine ⟨w,?_,?_,?_,?_,?_⟩
    · simp [Graph.write,storeLabel,ofEffect,TraceMemory.Access.effect,AccessKind.op]
    · simp [Graph.sameAddress,storeLabel,label,ofEffect,TraceMemory.Access.effect]
    · simp [storeLabel,label,ofEffect,TraceMemory.Access.effect]
    · dsimp only
      rw [wrank]
      have rrank : eventRank n input scratch ((graph input scratch (canonicalTrace cfg input scratch seeds) source co).event r) =
          rankBase input scratch + (2*n+i) := by
        simp [label,eventRank,ofEffect_pointer cfg .shared .load i _ (Nat.le_of_lt inside),
          TraceMemory.Access.effect,Location.code,slot,effectRank,AccessKind.op]
        omega
      rw [rrank]
      omega
    · intro v write same
      have address : ((graph input scratch (canonicalTrace cfg input scratch seeds) source co).event v).effect.address =
          (⟨1,i⟩ : Location 2).code := by
        simpa [Graph.sameAddress,label,ofEffect_pointer cfg .shared .load i _ (Nat.le_of_lt inside),
          TraceMemory.Access.effect,slot] using same
      dsimp only
      rw [wrank]
      exact canonical_shared_latest cfg input scratch seeds inputs storage source co v write i inside address

theorem canonical_base_before (cfg : Config n) (input scratch : List Word) (seeds : Fin n → Seed)
    (inputs : n < input.length) (storage : n ≤ scratch.length) (source co)
    (a b : Fin (labels input scratch (canonicalTrace cfg input scratch seeds)).length)
    (edge : Graph.Ordered.baseEdge (graph input scratch (canonicalTrace cfg input scratch seeds) source co)
      (extra input scratch (canonicalTrace cfg input scratch seeds) source co) a b) :
    eventRank n input scratch ((graph input scratch (canonicalTrace cfg input scratch seeds) source co).event a) <
      eventRank n input scratch ((graph input scratch (canonicalTrace cfg input scratch seeds) source co).event b) := by
  let g := graph input scratch (canonicalTrace cfg input scratch seeds) source co
  have noRelease : ∀ w, ¬g.release w := by
    intro w release
    have write : g.write w := by
      change (g.event w).effect.op = .store .release at release
      simp [Graph.write,release]
    have notInitial : ¬g.initial w := by
      intro initial
      have a : (g.event w).effect.op = .init := initial
      have b : (g.event w).effect.op = .store .release := release
      rw [a] at b
      contradiction
    rcases canonical_write cfg input scratch seeds inputs storage source co w write notInitial with
      ⟨t,position,label⟩ | ⟨position,label⟩
    all_goals
      change (g.event w).effect.op = .store .release at release
      change g.event w = _ at label
      simp [label,ofEffect,TraceMemory.Access.effect,AccessKind.op] at release
  have endpoints : (g.event a).thread ≠ none ∧ (g.event b).thread ≠ none ∧
      (g.event a).position < (g.event b).position := by
    rcases edge with (po | sync) | barrier
    · exact ⟨po.1,by rw [← po.2.1]; exact po.1,po.2.2⟩
    · obtain ⟨_,w,r,pattern,_⟩ := sync
      rcases pattern with ⟨_,release⟩ | ⟨release,_⟩ <;> exact False.elim (noRelease a release)
    · exact ⟨(barrier_order_noninitial _ _ _ barrier).1,
        (barrier_order_noninitial _ _ _ barrier).2,barrier_order_increases _ _ _ barrier⟩
  have ranks := canonical_program_rank cfg input scratch seeds inputs storage source co a b
    endpoints.1 endpoints.2.1 endpoints.2.2
  change eventRank n input scratch (g.event a) < eventRank n input scratch (g.event b)
  change effectRank n (g.event a).effect < effectRank n (g.event b).effect at ranks
  cases ha : (g.event a).thread <;> cases hb : (g.event b).thread <;>
    simp_all [eventRank]

theorem canonical_initial_before (cfg : Config n) (input scratch : List Word) (seeds : Fin n → Seed)
    (source co) (i w : Fin (labels input scratch (canonicalTrace cfg input scratch seeds)).length)
    (initial : (graph input scratch (canonicalTrace cfg input scratch seeds) source co).initial i)
    (same : (graph input scratch (canonicalTrace cfg input scratch seeds) source co).sameAddress i w)
    (different : i ≠ w) :
    eventRank n input scratch ((graph input scratch (canonicalTrace cfg input scratch seeds) source co).event i) <
      eventRank n input scratch ((graph input scratch (canonicalTrace cfg input scratch seeds) source co).event w) := by
  obtain ⟨iv,hi,li⟩ := initial_event_origin input scratch _ source co i
    ((graph_initial_iff input scratch _ source co i).mp initial)
  by_cases noneThread : ((graph input scratch (canonicalTrace cfg input scratch seeds) source co).event w).thread = none
  · obtain ⟨wv,hw,lw⟩ := initial_event_origin input scratch _ source co w noneThread
    have locations : iv.location.code = wv.location.code := by simpa [Graph.sameAddress,li,lw,Initial.occurrence] using same
    apply False.elim
    apply different
    apply graph_identity_injective input scratch _ source co
    simp [li,lw,identity,Initial.occurrence,locations]
  · have bound := initial_rank_bound input scratch iv hi
    cases ht : ((graph input scratch (canonicalTrace cfg input scratch seeds) source co).event w).thread with
    | none => exact False.elim (noneThread ht)
    | some t =>
      simp only [li,Initial.occurrence,eventRank,ht]
      exact Nat.lt_of_lt_of_le bound (Nat.le_add_right _ _)

/-- Actual canonical execution admits concrete source/coherence choices satisfying
all ordered whole-word constraints and a separate conservative grounding rank.
No read value, source identity, final sum, or validity premise is assumed. -/
theorem canonical_valid_exists (cfg : Config n) (input scratch : List Word) (seeds : Fin n → Seed)
    (inputs : n < input.length) (storage : n ≤ scratch.length) :
    ∃ source co,
      let g := graph input scratch (canonicalTrace cfg input scratch seeds) source co
      let order := extra input scratch (canonicalTrace cfg input scratch seeds) source co
      Graph.Ordered.Valid g order ∧ ∀ a, ¬Path (grounding g order) a a := by
  classical
  let g0 := graph input scratch (canonicalTrace cfg input scratch seeds) (fun i => i) (fun _ _ => false)
  let rank := fun i => eventRank n input scratch (g0.event i)
  have existsSource := canonical_source_exists cfg input scratch seeds inputs storage (fun i => i) (fun _ _ => false)
  let source := fun r => if hr : g0.read r then Classical.choose (existsSource r hr) else r
  let co := fun a b => decide (g0.write a ∧ g0.write b ∧ g0.sameAddress a b ∧ rank a < rank b)
  let g := graph input scratch (canonicalTrace cfg input scratch seeds) source co
  let order := extra input scratch (canonicalTrace cfg input scratch seeds) source co
  have chosen (r) (read : g.read r) :
      g.write (g.source r) ∧ g.sameAddress (g.source r) r ∧
      (g.event (g.source r)).effect.value = (g.event r).effect.value ∧
      rank (g.source r) < rank r ∧
      (∀ v, g.write v → g.sameAddress v r → rank v ≤ rank (g.source r)) := by
    have hr : g0.read r := read
    have spec := Classical.choose_spec (existsSource r hr)
    have eq : source r = Classical.choose (existsSource r hr) := dite_eq_left hr
    change g.write (source r) ∧ g.sameAddress (source r) r ∧
      (g.event (source r)).effect.value = (g.event r).effect.value ∧
      rank (source r) < rank r ∧ (∀ v, g.write v → g.sameAddress v r → rank v ≤ rank (source r))
    rw [eq]
    exact spec
  have cert : SerialCertificate g order rank := {
    injective := canonical_rank_injective cfg input scratch seeds inputs storage source co
    sources := ⟨fun r read => ⟨(chosen r read).1,(chosen r read).2.1,(chosen r read).2.2.1⟩⟩
    source_before := fun r read => (chosen r read).2.2.2.1
    latest := fun w r write read same _ => (chosen r read).2.2.2.2 w write same
    coherence_iff := by
      intro a b
      change decide (g0.write a ∧ g0.write b ∧ g0.sameAddress a b ∧ rank a < rank b) = true ↔ _
      exact decide_eq_true_iff
    initial_before := fun i w initial _ same different =>
      canonical_initial_before cfg input scratch seeds source co i w initial same different
    base_before := canonical_base_before cfg input scratch seeds inputs storage source co
  }
  exact ⟨source,co,cert.valid,cert.grounded⟩

end Ptx.Scalar.SharedReduction.Machine.Memory

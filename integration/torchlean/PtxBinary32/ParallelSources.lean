import PtxBinary32.ParallelChronology

/-! Construct read sources from a concrete-read execution, retaining their exact
indices in the existing memory graph and proving latest-write chronology. -/
namespace Ptx.Scalar.Parallel.Memory.Chronology
open Ptx.TraceMemory
variable {n : Nat} {events : List (Event n)} {program : List Instr} {global shared : List Word}

/-- Split a trace at an observed event, retaining its numeric position. -/
theorem split_at (atE : (events : List (Event n))[position]? = some e) :
    ∃ before after, events = before++e::after ∧ before.length=position := by
  induction events generalizing position with
  | nil => simp at atE
  | cons head rest ih =>
    cases position with
    | zero =>
      have eq : head=e := by simpa using atE
      subst head
      exact ⟨[],rest,rfl,rfl⟩
    | succ p =>
      obtain ⟨before,after,eq,len⟩ := ih (by simpa using atE)
      exact ⟨head::before,after,by simp [eq],by simp [len]⟩

theorem initial_member (space : Space) (index : Nat) (value : Word)
    (read : (Replay.arena ⟨global,shared⟩ space)[index]? = some value) :
    (⟨⟨slot space,index⟩,value⟩ : Initial 2) ∈ Prior.initial global shared := by
  cases space <;> simp only [Replay.arena] at read
  all_goals
    obtain ⟨bound,eq⟩ := List.getElem?_eq_some_iff.mp read
    simp only [Prior.initial,SharedReduction.Machine.Memory.initial,List.mem_append,slot]
  · exact .inl (List.mem_mapIdx.mpr ⟨index,bound,by simp [eq]⟩)
  · exact .inr (List.mem_mapIdx.mpr ⟨index,bound,by simp [eq]⟩)

theorem initial_graph_member (space : Space) (index : Nat) (value : Word)
    (read : (Replay.arena ⟨global,shared⟩ space)[index]? = some value) (source co) :
    ∃ w : Fin (labels program global shared events).length,
      (graph program global shared events source co).event w =
        (⟨⟨slot space,index⟩,value⟩ : Initial 2).occurrence := by
  have member : (⟨⟨slot space,index⟩,value⟩ : Initial 2).occurrence ∈ labels program global shared events := by
    apply (events_member_iff _ _ _ _ _).mpr
    exact .inl ⟨_,initial_member space index value read,rfl⟩
  obtain ⟨w,bound,label⟩ := List.mem_iff_getElem.mp member
  exact ⟨⟨w,bound⟩,label⟩

/-- A same-location program store is recognized by the replay source tracker. -/
theorem writtenAt_of_address (space seen : Space) (address : Address) (occ : Scalar.Occurrence)
    (eff : MemoryEffect) (t : Fin n) (memory : occ.memory = some eff) (kind : eff.kind = .store)
    (same : (location seen eff.address).code = (location space address).code) :
    Replay.writtenAt space (address.toNat/4) (.scalar t (some seen) occ) = some eff.value := by
  have loc := Location.code_injective same
  have slots := congrArg Location.storage loc
  have word := congrArg Location.word loc
  have spaces : seen=space := by cases seen <;> cases space <;> simp_all [location,slot]
  subst seen
  simp [Replay.writtenAt,memory,kind,show eff.address.toNat/4=address.toNat/4 from word]

/-- Read compatibility, past-source and last-write obligations, independent of
any source/coherence fields that will later be installed in the graph. -/
def SourceFor (program : List Instr) (global shared : List Word) (events : List (Event n))
    (r w : Fin (labels program global shared events).length) : Prop :=
  let g := graph program global shared events id (fun _ _ => false)
  g.write w ∧ g.sameAddress w r ∧ (g.event w).effect.value=(g.event r).effect.value ∧
    rank global shared (g.event w)<rank global shared (g.event r) ∧
    ∀ v, g.write v → g.sameAddress v r → rank global shared (g.event v)<rank global shared (g.event r) →
      rank global shared (g.event v)≤rank global shared (g.event w)

/-- Every read in a concrete execution has a compatible last preceding graph
write. Desired values, writer identities and chronology are derived here. -/
theorem source_exists {cfg : Config n} {start final : State n}
    (run : ConcreteRuns cfg program start events final)
    (r : Fin (labels program start.global start.shared events).length)
    (read : (graph program start.global start.shared events id (fun _ _ => false)).read r) :
    ∃ w, SourceFor program start.global start.shared events r w := by
  let g := graph program start.global start.shared events id (fun _ _ => false)
  change g.read r at read
  change ∃ w, g.write w ∧ g.sameAddress w r ∧ (g.event w).effect.value=(g.event r).effect.value ∧
    rank start.global start.shared (g.event w)<rank start.global start.shared (g.event r) ∧
    ∀ v, g.write v → g.sameAddress v r → rank start.global start.shared (g.event v)<rank start.global start.shared (g.event r) →
      rank start.global start.shared (g.event v)≤rank start.global start.shared (g.event w)
  have mr := List.getElem_mem r.isLt (l := labels program start.global start.shared events)
  have tr : (g.event r).thread ≠ none := by
    intro h
    have init := (initial_iff mr).mpr h
    change (g.event r).effect.op = .init at init
    simp [Graph.read,init] at read
  obtain ⟨t,space,occ,eff,atR,memory,labelR⟩ := program_origin mr tr
  change events[(g.event r).position]? = _ at atR
  change g.event r = ⟨some t.val,(g.event r).position,(ofEffect space eff).effect⟩ at labelR
  have effectR := congrArg Ptx.Occurrence.effect labelR
  have kind : eff.kind = .load := by
    cases hk : eff.kind with
    | load => rfl
    | store =>
      change g.read r at read
      simp [Graph.read,effectR,ofEffect,hk,Access.effect,AccessKind.op] at read
  have load : occ.memory = some ⟨.load,eff.address,eff.value⟩ := by
    rw [memory]
    cases eff
    cases kind
    rfl
  obtain ⟨before,after,split,len⟩ := split_at atR
  have checked := Replay.concrete_replays run
  rw [split] at checked
  have origins := Replay.load_source (Replay.arrays start) (Replay.arrays final)
    before after t space occ eff.address eff.value load checked
  have threadR : (g.event r).thread = some t.val := congrArg Ptx.Occurrence.thread labelR
  have rankR : rank start.global start.shared (g.event r) =
      2*(start.global.length+start.shared.length)+before.length := by simp [rank,threadR,len]
  rcases origins with ⟨original,noWrites⟩ | ⟨pre,writer,suffix,splitBefore,written,noWrites⟩
  · obtain ⟨w,labelW⟩ := initial_graph_member (program := program) (events := events)
      space (eff.address.toNat/4) eff.value original id (fun _ _ => false)
    change g.event w = _ at labelW
    have rw : rank start.global start.shared (g.event w) = (location space eff.address).code := by
      simp [rank,labelW,Initial.occurrence,location]
    have wr : g.sameAddress w r := by simp [Graph.sameAddress,labelW,effectR,Initial.occurrence,ofEffect,Access.effect,location]
    refine ⟨w,?_,wr,?_,?_,?_⟩
    · simp [Graph.write,labelW,Initial.occurrence]
    · simp [labelW,effectR,Initial.occurrence,ofEffect,Access.effect]
    · have bound := initial_rank (List.getElem_mem w.isLt (l := labels program start.global start.shared events))
        (show (g.event w).thread = none by simp [labelW,Initial.occurrence])
      change rank start.global start.shared (g.event w) < _ at bound
      rw [rankR]; omega
    · intro v write same earlier
      have mv := List.getElem_mem v.isLt (l := labels program start.global start.shared events)
      by_cases tv : (g.event v).thread = none
      · have pos := initial_position mv tv
        have addr : (g.event v).effect.address = (location space eff.address).code := by
          simpa [Graph.sameAddress,effectR,ofEffect,Access.effect] using same
        rw [rw]
        change (g.event v).position = (g.event v).effect.address at pos
        simp [rank,tv,pos,addr]
      · have ni : ¬g.initial v := fun h => tv ((initial_iff mv).mp h)
        obtain ⟨u,p,seen,other,store,atV,_,_,memV,kindV,labelV⟩ :=
          program_write_origin program start.global start.shared events id (fun _ _ => false) v write ni
        change g.event v = _ at labelV
        have pos : p<before.length := by
          rw [rankR] at earlier
          simpa [rank,labelV] using earlier
        have atBefore : before[p]? = some (.scalar u (some seen) other) := by
          simpa [split,List.getElem?_append,pos] using atV
        have none := noWrites _ (List.mem_of_getElem? atBefore)
        have address : (location seen store.address).code = (location space eff.address).code := by
          simpa [Graph.sameAddress,labelV,effectR,ofEffect,Access.effect] using same
        rw [writtenAt_of_address space seen eff.address other store u memV kindV address] at none
        contradiction
  · obtain ⟨u,storeOcc,address,writerEq,storeMem,wordEq⟩ := Replay.writtenAt_some _ _ _ _ written
    have atW : events[pre.length]? = some (.scalar u (some space) storeOcc) := by
      simp [split,splitBefore,List.append_assoc,writerEq]
    obtain ⟨w,labelW⟩ := run_graph_complete run.toRuns id (fun _ _ => false) pre.length u space storeOcc
      ⟨.store,address,eff.value⟩ atW storeMem
    change g.event w = _ at labelW
    have rw : rank start.global start.shared (g.event w) =
        2*(start.global.length+start.shared.length)+pre.length := by simp [rank,labelW]
    have beforeBound : pre.length<before.length := by simp [splitBefore]
    have wr : g.sameAddress w r := by
      simp [Graph.sameAddress,labelW,effectR,ofEffect,Access.effect,location,Location.code,wordEq]
    refine ⟨w,?_,wr,?_,?_,?_⟩
    · simp [Graph.write,labelW,ofEffect,Access.effect,AccessKind.op]
    · simp [labelW,effectR,ofEffect,Access.effect]
    · rw [rw,rankR]; omega
    · intro v write same earlier
      have mv := List.getElem_mem v.isLt (l := labels program start.global start.shared events)
      by_cases tv : (g.event v).thread = none
      · have bound := initial_rank mv tv
        change rank start.global start.shared (g.event v) < _ at bound
        rw [rw]; omega
      · have ni : ¬g.initial v := fun h => tv ((initial_iff mv).mp h)
        obtain ⟨thread,p,seen,other,store,atV,_,_,memV,kindV,labelV⟩ :=
          program_write_origin program start.global start.shared events id (fun _ _ => false) v write ni
        change g.event v = _ at labelV
        have pos : p<before.length := by
          rw [rankR] at earlier
          simpa [rank,labelV] using earlier
        have atBefore : before[p]? = some (.scalar thread (some seen) other) := by
          simpa [split,List.getElem?_append,pos] using atV
        by_cases past : p≤pre.length
        · rw [rw]; simp [rank,labelV,past]
        · have inSuffix : suffix[p-(pre.length+1)]? = some (.scalar thread (some seen) other) := by
            have greater : ¬p<pre.length := by omega
            have positive : p-pre.length≠0 := by omega
            simpa [splitBefore,List.getElem?_append,greater,List.getElem?_cons,positive,Nat.sub_add_eq] using atBefore
          have none := noWrites _ (List.mem_of_getElem? inSuffix)
          have addr : (location seen store.address).code = (location space eff.address).code := by
            simpa [Graph.sameAddress,labelV,effectR,ofEffect,Access.effect] using same
          rw [writtenAt_of_address space seen eff.address other store thread memV kindV addr] at none
          contradiction

end Ptx.Scalar.Parallel.Memory.Chronology

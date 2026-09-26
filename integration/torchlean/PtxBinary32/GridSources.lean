import PtxBinary32.GridChronology
import PtxBinary32.GridReplay

/-! Last preceding stores in checked grid replay become sources in the one
combined graph. Neither values nor admission are supplied as assumptions. -/
namespace Ptx.Scalar.Parallel.Grid.Memory.Chronology
open Ptx.TraceMemory (Access Initial Projected Location AccessKind)
variable {groups n : Nat} {events : List (Grid.Event groups n)} {program : List Instr} {start : Grid.State groups n}

theorem split_at {events : List α} (atE : events[position]?=some e) :
    ∃ before after, events=before++e::after ∧ before.length=position := by
  induction events generalizing position with
  | nil => simp at atE
  | cons head rest ih =>
    cases position with
    | zero =>
      have eq : head=e := by simpa using atE
      subst head; exact ⟨[],rest,rfl,rfl⟩
    | succ p =>
      obtain ⟨before,after,eq,len⟩ := ih (by simpa using atE)
      exact ⟨head::before,after,by simp [eq],by simp [len]⟩

def cell (g : Fin groups) (space : Space) (index : Nat) : Location (groups+1) :=
  ⟨match space with | .global => 0 | .shared => ⟨g.val+1,by omega⟩,index⟩

theorem initial_member (g : Fin groups) (space : Space) (index : Nat) (value : Word)
    (read : (Replay.arena (Replay.arrays start) g space)[index]?=some value) :
    (⟨cell g space index,value⟩ : Initial (groups+1)) ∈ initials start := by
  cases space <;> simp only [Replay.arena,Replay.arrays] at read
  all_goals
    obtain ⟨bound,eq⟩ := List.getElem?_eq_some_iff.mp read
    simp only [initials,List.mem_append,cell]
  · exact .inl (List.mem_mapIdx.mpr ⟨index,bound,by simp [eq]⟩)
  · exact .inr (List.mem_flatMap.mpr ⟨g,List.mem_finRange g,List.mem_mapIdx.mpr ⟨index,bound,by simp [eq]⟩⟩)

theorem initial_graph_member (g : Fin groups) (space : Space) (index : Nat) (value : Word)
    (read : (Replay.arena (Replay.arrays start) g space)[index]?=some value) (source co) :
    ∃ w : Fin (labels program start events).length,
      (graph program start events source co).event w=(⟨cell g space index,value⟩ : Initial (groups+1)).occurrence := by
  have member : (⟨cell g space index,value⟩ : Initial (groups+1)).occurrence ∈ labels program start events := by
    apply List.mem_append_left
    exact List.mem_map.mpr ⟨_,initial_member g space index value read,rfl⟩
  obtain ⟨w,bound,label⟩ := List.mem_iff_getElem.mp member
  exact ⟨⟨w,bound⟩,label⟩

theorem writtenAt_of_address (g h : Fin groups) (space seen : Space) (address : Address)
    (occ : Scalar.Occurrence) (eff : MemoryEffect) (t : Fin n)
    (memory : occ.memory=some eff) (kind : eff.kind=.store)
    (same : (Grid.location h seen eff.address).code=(Grid.location g space address).code) :
    Replay.writtenAt g space (address.toNat/4) (h,.scalar t (some seen) occ)=some eff.value := by
  have loc := Location.code_injective same
  have slots := congrArg (fun l : Location (groups+1) => l.storage.val) loc
  have word := congrArg Location.word loc
  cases seen <;> cases space <;> simp only [Grid.location] at slots word
  · simp [Replay.writtenAt,Parallel.Replay.writtenAt,memory,kind,word]
  · simp at slots
  · simp at slots
  · have eq : h=g := Fin.ext (by omega)
    subst h
    simp [Replay.writtenAt,Parallel.Replay.writtenAt,memory,kind,word]

/-- Read compatibility, past-source and last-write obligations, independent of
any source/coherence fields that will later be installed in the graph. -/
def SourceFor (program : List Instr) (start : Grid.State groups n) (events : List (Grid.Event groups n))
    (r w : Fin (labels program start events).length) : Prop :=
  let gr := graph program start events id (fun _ _ => false)
  gr.write w ∧ gr.sameAddress w r ∧ (gr.event w).effect.value=(gr.event r).effect.value ∧
    rank start (gr.event w)<rank start (gr.event r) ∧
    ∀ v, gr.write v → gr.sameAddress v r → rank start (gr.event v)<rank start (gr.event r) →
      rank start (gr.event v)≤rank start (gr.event w)

/-- Every read in a concrete execution has a compatible last preceding graph
write. Desired values, writer identities and chronology are derived here. -/
theorem source_exists {cfg : Config n} {start final : Grid.State groups n}
    (run : Grid.ConcreteRuns cfg program start events final)
    (r : Fin (labels program start events).length)
    (read : (graph program start events id (fun _ _ => false)).read r) :
    ∃ w, SourceFor program start events r w := by
  let gr := graph program start events id (fun _ _ => false)
  change gr.read r at read
  change ∃ w, gr.write w ∧ gr.sameAddress w r ∧ (gr.event w).effect.value=(gr.event r).effect.value ∧
    rank start (gr.event w)<rank start (gr.event r) ∧
    ∀ v, gr.write v → gr.sameAddress v r → rank start (gr.event v)<rank start (gr.event r) →
      rank start (gr.event v)≤rank start (gr.event w)
  have mr := List.getElem_mem r.isLt (l := labels program start events)
  have tr : (gr.event r).thread ≠ none := by
    intro h
    have init := (initial_iff mr).mpr h
    change (gr.event r).effect.op = .init at init
    simp [Graph.read,init] at read
  obtain ⟨group,t,space,occ,eff,atR,memory,labelR⟩ := program_origin mr tr
  change events[(gr.event r).position]? = _ at atR
  change gr.event r = ⟨some (threadId group t),(gr.event r).position,(ofEffect group space eff).effect⟩ at labelR
  have effectR := congrArg Ptx.Occurrence.effect labelR
  have kind : eff.kind = .load := by
    cases hk : eff.kind with
    | load => rfl
    | store =>
      change gr.read r at read
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
    before after group t space occ eff.address eff.value load checked
  have threadR : (gr.event r).thread = some (threadId group t) := congrArg Ptx.Occurrence.thread labelR
  have rankR : rank start (gr.event r) =
      ceiling start+before.length := by simp [rank,threadR,len]
  rcases origins with ⟨original,noWrites⟩ | ⟨pre,writer,suffix,splitBefore,written,noWrites⟩
  · obtain ⟨w,labelW⟩ := initial_graph_member (program := program) (events := events)
      group space (eff.address.toNat/4) eff.value original id (fun _ _ => false)
    change gr.event w = _ at labelW
    have rw : rank start (gr.event w) = (Grid.location group space eff.address).code := by
      cases space <;> simp [rank,labelW,Initial.occurrence,Grid.location,cell]
    have wr : gr.sameAddress w r := by cases space <;> simp [Graph.sameAddress,labelW,effectR,Initial.occurrence,ofEffect,Access.effect,Grid.location,cell]
    refine ⟨w,?_,wr,?_,?_,?_⟩
    · simp [Graph.write,labelW,Initial.occurrence]
    · simp [labelW,effectR,Initial.occurrence,ofEffect,Access.effect]
    · have bound := initial_rank (List.getElem_mem w.isLt (l := labels program start events))
        (show (gr.event w).thread = none by simp [labelW,Initial.occurrence])
      change rank start (gr.event w) < _ at bound
      rw [rankR]; omega
    · intro v write same earlier
      have mv := List.getElem_mem v.isLt (l := labels program start events)
      by_cases tv : (gr.event v).thread = none
      · have pos := initial_position mv tv
        have addr : (gr.event v).effect.address = (Grid.location group space eff.address).code := by
          simpa [Graph.sameAddress,effectR,ofEffect,Access.effect] using same
        rw [rw]
        change (gr.event v).position = (gr.event v).effect.address at pos
        simp [rank,tv,pos,addr]
      · have ni : ¬gr.initial v := fun h => tv ((initial_iff mv).mp h)
        obtain ⟨otherGroup,u,p,seen,other,store,atV,_,_,memV,kindV,labelV⟩ :=
          program_write_origin program start events id (fun _ _ => false) v write ni
        change gr.event v = _ at labelV
        have pos : p<before.length := by
          rw [rankR] at earlier
          simpa [rank,labelV] using earlier
        have atBefore : before[p]? = some (otherGroup,.scalar u (some seen) other) := by
          simpa [split,List.getElem?_append,pos] using atV
        have none := noWrites _ (List.mem_of_getElem? atBefore)
        have address : (Grid.location otherGroup seen store.address).code = (Grid.location group space eff.address).code := by
          simpa [Graph.sameAddress,labelV,effectR,ofEffect,Access.effect] using same
        rw [writtenAt_of_address group otherGroup space seen eff.address other store u memV kindV address] at none
        contradiction
  · obtain ⟨writerGroup,u,storeOcc,address,writerEq,storeMem,wordEq,groupEq⟩ := Replay.writtenAt_some _ _ _ _ _ written
    have atW : events[pre.length]? = some (writerGroup,.scalar u (some space) storeOcc) := by
      simp [split,splitBefore,List.append_assoc,writerEq]
    obtain ⟨w,labelW⟩ := graph_complete run.toRuns id (fun _ _ => false) pre.length writerGroup u space storeOcc
      ⟨.store,address,eff.value⟩ atW storeMem
    change gr.event w = _ at labelW
    have rw : rank start (gr.event w) =
        ceiling start+pre.length := by simp [rank,labelW]
    have beforeBound : pre.length<before.length := by simp [splitBefore]
    have wr : gr.sameAddress w r := by
      rcases groupEq with hs | hg
      · subst space; simp [Graph.sameAddress,labelW,effectR,ofEffect,Access.effect,Grid.location,Location.code,wordEq]
      · subst writerGroup; simp [Graph.sameAddress,labelW,effectR,ofEffect,Access.effect,Grid.location,Location.code,wordEq]
    refine ⟨w,?_,wr,?_,?_,?_⟩
    · simp [Graph.write,labelW,ofEffect,Access.effect,AccessKind.op]
    · simp [labelW,effectR,ofEffect,Access.effect]
    · rw [rw,rankR]; omega
    · intro v write same earlier
      have mv := List.getElem_mem v.isLt (l := labels program start events)
      by_cases tv : (gr.event v).thread = none
      · have bound := initial_rank mv tv
        change rank start (gr.event v) < _ at bound
        rw [rw]; omega
      · have ni : ¬gr.initial v := fun h => tv ((initial_iff mv).mp h)
        obtain ⟨otherGroup,thread,p,seen,other,store,atV,_,_,memV,kindV,labelV⟩ :=
          program_write_origin program start events id (fun _ _ => false) v write ni
        change gr.event v = _ at labelV
        have pos : p<before.length := by
          rw [rankR] at earlier
          simpa [rank,labelV] using earlier
        have atBefore : before[p]? = some (otherGroup,.scalar thread (some seen) other) := by
          simpa [split,List.getElem?_append,pos] using atV
        by_cases past : p≤pre.length
        · rw [rw]; simp [rank,labelV,past]
        · have inSuffix : suffix[p-(pre.length+1)]? = some (otherGroup,.scalar thread (some seen) other) := by
            have greater : ¬p<pre.length := by omega
            have positive : p-pre.length≠0 := by omega
            simpa [splitBefore,List.getElem?_append,greater,List.getElem?_cons,positive,Nat.sub_add_eq] using atBefore
          have none := noWrites _ (List.mem_of_getElem? inSuffix)
          have addr : (Grid.location otherGroup seen store.address).code = (Grid.location group space eff.address).code := by
            simpa [Graph.sameAddress,labelV,effectR,ofEffect,Access.effect] using same
          rw [writtenAt_of_address group otherGroup space seen eff.address other store thread memV kindV addr] at none
          contradiction

end Ptx.Scalar.Parallel.Grid.Memory.Chronology

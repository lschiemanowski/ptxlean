import PtxBinary32.ParallelUnaryChronology

/-! A sufficient admission certificate for pointwise traces. Its hypotheses
are facts about emitted reads and stores, proved from a selected execution;
universal candidates retain the original memory constraints. -/
namespace Ptx.Scalar.ParallelUnary.Memory.Chronology
open Ptx.TraceMemory
variable {n : Nat} {events : List (Event n)} {program : List Instr} {global : List Word}

/-- Actual reads return initialized words, each within the arena. -/
def InitialReads (global : List Word) (events : List (Event n)) : Prop :=
  ∀ t occ effect, .scalar t occ ∈ events → occ.memory=some effect → effect.kind=.load →
    effect.address.toNat/4<global.length ∧ effect.value=global[effect.address.toNat/4]!

/-- Every program store to a read location occurs later in this selected trace. -/
def FutureStores (events : List (Event n)) : Prop :=
  ∀ (p q : Nat) (e f : Event n) (a b : MemoryEffect), events[p]?=some e → events[q]?=some f →
    e.memory=some a → f.memory=some b → a.kind=.load → b.kind=.store →
    a.address.toNat/4=b.address.toNat/4 → p<q

theorem initial_graph_member (index : Nat) (bound : index<global.length) (source co) :
    ∃ w : Fin (labels program global events).length,
      (graph program global events source co).event w =
        (⟨⟨0,index⟩,global[index]!⟩ : Initial 2).occurrence := by
  have inside : (⟨⟨0,index⟩,global[index]!⟩ : Initial 2)∈initial global := by
    simp only [initial,SharedReduction.Machine.Memory.initial,List.mem_append]
    exact .inl (List.mem_mapIdx.mpr ⟨index,bound,by simp [List.getElem?_eq_getElem bound]⟩)
  have member : (⟨⟨0,index⟩,global[index]!⟩ : Initial 2).occurrence∈labels program global events := by
    apply (events_member_iff _ _ _ _ _).mpr
    exact .inl ⟨_,inside,rfl⟩
  obtain ⟨w,bound,label⟩ := List.mem_iff_getElem.mp member
  exact ⟨⟨w,bound⟩,label⟩

def SourceFor (program : List Instr) (global : List Word) (events : List (Event n))
    (r w : Fin (labels program global events).length) : Prop :=
  let g := graph program global events id (fun _ _ => false)
  g.write w ∧ g.sameAddress w r ∧ (g.event w).effect.value=(g.event r).effect.value ∧
    rank global (g.event w)<rank global (g.event r) ∧
    ∀ v, g.write v → g.sameAddress v r → rank global (g.event v)<rank global (g.event r) →
      rank global (g.event v)≤rank global (g.event w)

/-- The initialized source is compatible and no program write precedes its read. -/
theorem source_exists (reads : InitialReads global events) (future : FutureStores events)
    (r : Fin (labels program global events).length)
    (read : (graph program global events id (fun _ _ => false)).read r) :
    ∃ w, SourceFor program global events r w := by
  let g := graph program global events id (fun _ _ => false)
  change g.read r at read
  change ∃ w, g.write w ∧ g.sameAddress w r ∧ (g.event w).effect.value=(g.event r).effect.value ∧
    rank global (g.event w)<rank global (g.event r) ∧
    ∀ v, g.write v → g.sameAddress v r → rank global (g.event v)<rank global (g.event r) →
      rank global (g.event v)≤rank global (g.event w)
  have mr := List.getElem_mem r.isLt (l := labels program global events)
  have tr : (g.event r).thread ≠ none := by
    intro h
    have init := (initial_iff mr).mpr h
    change (g.event r).effect.op = .init at init
    simp [Graph.read,init] at read
  obtain ⟨t,occ,eff,atR,memory,labelR⟩ := program_origin mr tr
  change events[(g.event r).position]? = _ at atR
  change g.event r = ⟨some t.val,(g.event r).position,(ofEffect eff).effect⟩ at labelR
  have effectR := congrArg Ptx.Occurrence.effect labelR
  have kind : eff.kind=.load := by
    cases hk : eff.kind with
    | load => rfl
    | store => simp [Graph.read,effectR,ofEffect,Parallel.Memory.ofEffect,hk,Access.effect,AccessKind.op] at read
  obtain ⟨bound,value⟩ := reads t occ eff (List.mem_of_getElem? atR) memory kind
  obtain ⟨w,labelW⟩ := initial_graph_member (program:=program) (events:=events)
    (eff.address.toNat/4) bound id (fun _ _ => false)
  change g.event w = _ at labelW
  have rw : rank global (g.event w)=(⟨0,eff.address.toNat/4⟩ : Location 2).code := by
    simp [rank,labelW,Initial.occurrence]
  have wr : g.sameAddress w r := by
    simp [Graph.sameAddress,labelW,effectR,Initial.occurrence,ofEffect,Parallel.Memory.ofEffect,Access.effect,Parallel.Memory.location,Parallel.Memory.slot]
  refine ⟨w,?_,wr,?_,?_,?_⟩
  · simp [Graph.write,labelW,Initial.occurrence]
  · simp [labelW,effectR,Initial.occurrence,ofEffect,Parallel.Memory.ofEffect,Access.effect,value]
  · have earlier := initial_rank (List.getElem_mem w.isLt (l:=labels program global events))
      (show (g.event w).thread=none by simp [labelW,Initial.occurrence])
    change rank global (g.event w)<_ at earlier
    have rr : rank global (g.event r)=2*global.length+(g.event r).position := by simp [rank,tr]
    rw [rr]
    omega
  · intro v write same earlier
    have mv := List.getElem_mem v.isLt (l:=labels program global events)
    by_cases tv : (g.event v).thread=none
    · have pos := initial_position mv tv
      have addr : (g.event v).effect.address=(⟨0,eff.address.toNat/4⟩ : Location 2).code := by
        simpa [Graph.sameAddress,effectR,ofEffect,Parallel.Memory.ofEffect,Access.effect,Parallel.Memory.location,Parallel.Memory.slot] using same
      rw [rw]
      change (g.event v).position=(g.event v).effect.address at pos
      simp [rank,tv,pos,addr]
    · have ni : ¬g.initial v := fun h => tv ((initial_iff mv).mp h)
      obtain ⟨u,p,other,store,atV,_,_,memV,kindV,labelV⟩ :=
        program_write_origin program global events id (fun _ _ => false) v write ni
      change g.event v = _ at labelV
      have address : eff.address.toNat/4=store.address.toNat/4 := by
        have code : (⟨0,store.address.toNat/4⟩ : Location 2).code=(⟨0,eff.address.toNat/4⟩ : Location 2).code := by
          simpa [Graph.sameAddress,labelV,effectR,ofEffect,Parallel.Memory.ofEffect,Access.effect,Parallel.Memory.location,Parallel.Memory.slot] using same
        exact (congrArg Location.word (Location.code_injective code)).symm
      have later := future _ _ _ _ _ _ atR atV memory memV kind kindV address
      have pos : p<(g.event r).position := by
        simpa [rank,tr,labelV] using earlier
      omega

noncomputable def chosenSource (reads : InitialReads global events) (future : FutureStores events)
    (r : Fin (labels program global events).length) : Fin (labels program global events).length :=
  if h : (graph program global events id (fun _ _ => false)).read r
  then Classical.choose (source_exists reads future r h) else r

noncomputable def chronologicalCoherence (program : List Instr) (global : List Word)
    (events : List (Event n)) (a b : Fin (labels program global events).length) : Bool := by
  classical
  let g := graph program global events id (fun _ _ => false)
  exact decide (g.write a ∧ g.write b ∧ g.sameAddress a b ∧ rank global (g.event a)<rank global (g.event b))

theorem chosenSource_spec (reads : InitialReads global events) (future : FutureStores events)
    (r : Fin (labels program global events).length)
    (read : (graph program global events id (fun _ _ => false)).read r) :
    SourceFor program global events r (chosenSource reads future r) := by
  rw [chosenSource,dite_eq_left read]
  exact Classical.choose_spec (source_exists reads future r read)

theorem initial_certificate (reads : InitialReads global events) (future : FutureStores events) :
    SharedReduction.Machine.Memory.SerialCertificate
      (graph program global events (chosenSource reads future)
        (chronologicalCoherence program global events)) (fun _ _ => False)
      (fun i => rank global (labels program global events)[i.val]) := by
  classical
  let g := graph program global events (chosenSource reads future)
    (chronologicalCoherence program global events)
  have spec : ∀ r, g.read r → SourceFor program global events r (g.source r) :=
    fun r read => chosenSource_spec reads future r read
  refine {
    injective := rank_injective program global events
    sources := ⟨fun r read => ⟨(spec r read).1,(spec r read).2.1,(spec r read).2.2.1⟩⟩
    source_before := fun r read => (spec r read).2.2.2.1
    latest := fun w r write read same before => (spec r read).2.2.2.2 w write same before
    coherence_iff := ?_
    initial_before := ?_
    base_before := ?_
  }
  · intro a b
    change chronologicalCoherence program global events a b = true ↔ _
    unfold chronologicalCoherence
    exact @decide_eq_true_iff _ _
  · intro i w hi _ same ne
    exact initial_before program global events (chosenSource reads future)
      (chronologicalCoherence program global events) i w hi same ne
  · intro a b edge
    exact base_before program global events (chosenSource reads future)
      (chronologicalCoherence program global events) a b edge

/-- Sources and coherence are constructed; admission is not a witness premise. -/
theorem admitted_of_initial_reads (reads : InitialReads global events) (future : FutureStores events) :
    ∃ source co, Admitted program global events source co ∧
      ∀ i, ¬Path (SharedReduction.Machine.Memory.grounding
        (graph program global events source co) (fun _ _ => False)) i i := by
  let cert := initial_certificate (program:=program) reads future
  exact ⟨chosenSource reads future,chronologicalCoherence program global events,cert.valid,cert.grounded⟩

end Ptx.Scalar.ParallelUnary.Memory.Chronology

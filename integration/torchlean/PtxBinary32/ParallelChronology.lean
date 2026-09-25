import PtxBinary32.ParallelMemory
import PtxBinary32.ParallelReplaySources
import Ptx.SharedReductionMemoryWitness

/-! Chronological ranks for the actual combined global/shared memory labels.
Initial writes occupy a disjoint earlier range; program ranks retain positions
in the full instruction trace, including barriers and non-memory instructions. -/
namespace Ptx.Scalar.Parallel.Memory.Chronology
open Ptx.TraceMemory

variable {n : Nat} {events : List (Event n)} {program : List Instr} {global shared : List Word}
  {a b e : Ptx.Occurrence}

def rank (global shared : List Word) (e : Ptx.Occurrence) : Nat :=
  if e.thread = none then e.position else 2*(global.length+shared.length)+e.position

/-- A noninitial label recovers one actual scalar memory event. -/
theorem program_origin (member : e ∈ labels program global shared events) (thread : e.thread ≠ none) :
    ∃ t space occ eff,
      (events : List (Event n))[e.position]? = some (.scalar t (some space) occ) ∧
      occ.memory = some eff ∧ e = ⟨some t.val,e.position,(ofEffect space eff).effect⟩ := by
  rcases labels_origin program global shared events e member with ⟨i,_,eq⟩ | ⟨t,_,p,atP,accessP,eq⟩
  · simp [← eq,Initial.occurrence] at thread
  · obtain ⟨t',space,occ,eff,origin,tid,_,_,mem,_,val⟩ := access_origin program t p.origin p.access accessP
    refine ⟨t',space,occ,eff,?_,mem,?_⟩
    · simpa [← eq,Projected.occurrence,origin] using atP
    · rw [← eq]; simp [Projected.occurrence,val,tid]

theorem initial_origin (member : e ∈ labels program global shared events) (thread : e.thread = none) :
    ∃ i ∈ Prior.initial global shared, e = i.occurrence := by
  rcases labels_origin program global shared events e member with ⟨i,hi,eq⟩ | ⟨t,_,p,_,_,eq⟩
  · exact ⟨i,hi,eq.symm⟩
  · simp [← eq,Projected.occurrence] at thread

theorem initial_bound (i : Initial 2) (member : i ∈ Prior.initial global shared) :
    i.location.code < 2*(global.length+shared.length) := by
  simp only [Prior.initial,SharedReduction.Machine.Memory.initial,List.mem_append,List.mem_mapIdx] at member
  rcases member with ⟨j,hj,eq⟩ | ⟨j,hj,eq⟩
  all_goals subst i; simp only [Location.code]; omega

theorem initial_rank (member : e ∈ labels program global shared events) (thread : e.thread = none) :
    rank global shared e < 2*(global.length+shared.length) := by
  obtain ⟨i,hi,rfl⟩ := initial_origin member thread
  exact initial_bound i hi

theorem program_same_position (ha : a ∈ labels program global shared events)
    (hb : b ∈ labels program global shared events) (ta : a.thread ≠ none) (tb : b.thread ≠ none)
    (position : a.position=b.position) : a=b := by
  obtain ⟨t,space,occ,eff,atA,memA,labelA⟩ := program_origin ha ta
  obtain ⟨u,seen,other,eff',atB,memB,labelB⟩ := program_origin hb tb
  rw [← position,atA] at atB
  have eq := Event.scalar.inj (Option.some.inj atB)
  obtain ⟨rfl,seenEq,rfl⟩ := eq
  cases Option.some.inj seenEq
  rw [memA] at memB
  cases Option.some.inj memB
  rw [labelA,labelB,position]

theorem rank_injective (program : List Instr) (global shared : List Word) (events : List (Event n)) :
    Function.Injective (fun i : Fin (labels program global shared events).length => rank global shared (labels program global shared events)[i.val]) := by
  intro a b equal
  have ma := List.getElem_mem a.isLt (l := labels program global shared events)
  have mb := List.getElem_mem b.isLt (l := labels program global shared events)
  have unique := labels_unique program global shared events
  have identityEq : identity (labels program global shared events)[a.val] = identity (labels program global shared events)[b.val] := by
    by_cases ta : (labels program global shared events)[a.val].thread = none <;>
      by_cases tb : (labels program global shared events)[b.val].thread = none
    · simp [rank,ta,tb] at equal
      simp [identity,ta,tb,equal]
    · have bound := initial_rank ma ta
      simp [rank,ta,tb] at equal bound
      omega
    · have bound := initial_rank mb tb
      simp [rank,ta,tb] at equal bound
      omega
    · have pos : (labels program global shared events)[a.val].position = (labels program global shared events)[b.val].position := by
        simpa [rank,ta,tb] using equal
      rw [program_same_position ma mb ta tb pos]
  have eq : a.val=b.val := by
    apply unique.eq_of_getElem_eq (by simp) (by simp)
    simpa using identityEq
  exact Fin.ext eq

/-- Chronological program events have increasing ranks regardless of thread. -/
theorem program_before (ta : a.thread ≠ none) (tb : b.thread ≠ none) (pos : a.position < b.position) :
    rank global shared a < rank global shared b := by simp [rank,ta,tb,pos]

theorem initial_iff (member : e ∈ labels program global shared events) :
    e.effect.op = .init ↔ e.thread = none := by
  by_cases thread : e.thread = none
  · obtain ⟨i,_,rfl⟩ := initial_origin member thread
    simp [Initial.occurrence]
  · obtain ⟨t,space,occ,eff,_,_,eq⟩ := program_origin member thread
    rw [eq]
    cases hk : eff.kind <;> simp [ofEffect,Access.effect,AccessKind.op,hk]

theorem no_release (member : e ∈ labels program global shared events) : e.effect.op ≠ .store .release := by
  by_cases thread : e.thread = none
  · rw [(initial_iff member).mpr thread]; decide
  · obtain ⟨t,space,occ,eff,_,_,eq⟩ := program_origin member thread
    rw [eq]
    cases hk : eff.kind <;> simp [ofEffect,Access.effect,AccessKind.op,hk]

theorem initial_position (member : e ∈ labels program global shared events) (thread : e.thread = none) :
    e.position=e.effect.address := by
  obtain ⟨i,_,rfl⟩ := initial_origin member thread
  rfl

theorem initial_before (program : List Instr) (global shared : List Word) (events : List (Event n))
    (source co) (i w : Fin (labels program global shared events).length)
    (hi : (graph program global shared events source co).initial i)
    (same : (graph program global shared events source co).sameAddress i w) (ne : i≠w) :
    rank global shared ((graph program global shared events source co).event i) <
      rank global shared ((graph program global shared events source co).event w) := by
  have mi := List.getElem_mem i.isLt (l := labels program global shared events)
  have mw := List.getElem_mem w.isLt (l := labels program global shared events)
  have ti := (initial_iff mi).mp hi
  by_cases tw : ((graph program global shared events source co).event w).thread = none
  · have pi := initial_position mi ti
    have pw := initial_position mw tw
    have eq : rank global shared ((graph program global shared events source co).event i) =
        rank global shared ((graph program global shared events source co).event w) := by
      simp only [Graph.sameAddress] at same
      change (labels program global shared events)[i.val].effect.address =
        (labels program global shared events)[w.val].effect.address at same
      change (labels program global shared events)[w.val].thread = none at tw
      simp [graph,TraceMemory.graph,rank,ti,tw,pi,pw,same]
    exact False.elim (ne (rank_injective program global shared events eq))
  · have bound := initial_rank mi ti
    change rank global shared (labels program global shared events)[i.val] < _
    have wr : rank global shared ((graph program global shared events source co).event w) =
        2*(global.length+shared.length)+((graph program global shared events source co).event w).position := by
      simp [rank,tw]
    rw [wr]
    omega

theorem base_before (program : List Instr) (global shared : List Word) (events : List (Event n))
    (complete : History.CompleteOrigins events) (source co)
    (a b : Fin (labels program global shared events).length)
    (edge : Graph.Ordered.baseEdge (graph program global shared events source co)
      (order complete (graph program global shared events source co)).cross a b) :
    rank global shared ((graph program global shared events source co).event a) <
      rank global shared ((graph program global shared events source co).event b) := by
  rcases edge with (po | sync) | cross
  · exact program_before po.1 (by rw [← po.2.1]; exact po.1) po.2.2
  · obtain ⟨_,w,r,release,_⟩ := sync
    have no := no_release (List.getElem_mem a.isLt (l := labels program global shared events))
    rcases release with ⟨_,rel⟩ | ⟨rel,_⟩ <;> exact False.elim (no rel)
  · have pos := (order complete (graph program global shared events source co)).cross_increases cross
    change 3*((graph program global shared events source co).event a).position <
      3*((graph program global shared events source co).event b).position at pos
    obtain ⟨phase,ta,tb,ha,hb⟩ := cross
    have threadA : ((graph program global shared events source co).event a).thread ≠ none := by
      intro no
      have issuer := ha.1
      have participant := ha.2.1
      change ta.isSome at participant
      change owner n ((graph program global shared events source co).event a) = ta at issuer
      simp [owner,no] at issuer
      simp [← issuer] at participant
    have threadB : ((graph program global shared events source co).event b).thread ≠ none := by
      intro no
      have issuer := hb.1
      have participant := hb.2.1
      change tb.isSome at participant
      change owner n ((graph program global shared events source co).event b) = tb at issuer
      simp [owner,no] at issuer
      simp [← issuer] at participant
    exact program_before threadA threadB (by omega)

end Ptx.Scalar.Parallel.Memory.Chronology

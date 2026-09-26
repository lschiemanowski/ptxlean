import PtxBinary32.GridGraphUnique
import Ptx.SharedReductionMemoryWitness

/-! Chronological ranks for the actual combined global/shared memory labels.
Initial writes occupy a disjoint earlier range; program ranks retain positions
in the full instruction trace, including barriers and non-memory instructions. -/
namespace Ptx.Scalar.Parallel.Grid.Memory.Chronology
open Ptx.TraceMemory

variable {groups n : Nat} {events : List (Grid.Event groups n)} {program : List Instr} {start : Grid.State groups n}
  {a b e : Ptx.Occurrence}

/-- A finite ceiling larger than every explicit initial location code. -/
def ceiling (start : Grid.State groups n) : Nat := 1+((initials start).map (fun i => i.location.code)).sum

def rank (start : Grid.State groups n) (e : Ptx.Occurrence) : Nat :=
  if e.thread=none then e.position else ceiling start+e.position

theorem program_origin (member : e ∈ labels program start events) (thread : e.thread ≠ none) :
    ∃ g t space occ eff, events[e.position]?=some (g,.scalar t (some space) occ) ∧
      occ.memory=some eff ∧ e=⟨some (threadId g t),e.position,(ofEffect g space eff).effect⟩ := by
  rcases labels_origin program start events e member with ⟨i,_,eq⟩ | ⟨p,atP,accessP,eq⟩
  · simp [eq,Initial.occurrence] at thread
  · obtain ⟨g,t,space,occ,eff,origin,_,_,mem,_,val⟩ := access_origin program p.origin p.access accessP
    refine ⟨g,t,space,occ,eff,?_,mem,?_⟩
    · simpa [eq,label,origin] using atP
    · rw [eq]; simp [label,val,origin,owner]

theorem initial_origin (member : e ∈ labels program start events) (thread : e.thread=none) :
    ∃ i ∈ initials start, e=i.occurrence := by
  rcases labels_origin program start events e member with ⟨i,hi,eq⟩ | ⟨p,_,ha,eq⟩
  · exact ⟨i,hi,eq⟩
  · obtain ⟨g,t,space,occ,eff,origin,_⟩ := access_origin program p.origin p.access ha
    simp [eq,label,origin,owner] at thread

theorem initial_bound (i : Initial (groups+1)) (member : i ∈ initials start) : i.location.code<ceiling start := by
  have mem : i.location.code ∈ (initials start).map (fun i => i.location.code) := List.mem_map.mpr ⟨i,member,rfl⟩
  have bound := List.le_sum_of_mem mem
  unfold ceiling; omega

theorem initial_rank (member : e ∈ labels program start events) (thread : e.thread=none) :
    rank start e<ceiling start := by
  obtain ⟨i,hi,rfl⟩ := initial_origin member thread
  exact initial_bound i hi

theorem program_same_position (ha : a ∈ labels program start events) (hb : b ∈ labels program start events)
    (ta : a.thread≠none) (tb : b.thread≠none) (position : a.position=b.position) : a=b := by
  obtain ⟨g,t,space,occ,eff,atA,memA,labelA⟩ := program_origin ha ta
  obtain ⟨h,u,seen,other,eff',atB,memB,labelB⟩ := program_origin hb tb
  rw [← position,atA] at atB
  obtain ⟨rfl,evt⟩ := Prod.mk.inj (Option.some.inj atB)
  obtain ⟨rfl,seenEq,rfl⟩ := Parallel.Event.scalar.inj evt
  cases Option.some.inj seenEq
  rw [memA] at memB
  cases Option.some.inj memB
  rw [labelA,labelB,position]

theorem rank_injective (program : List Instr) (start : Grid.State groups n) (events : List (Grid.Event groups n)) :
    Function.Injective (fun i : Fin (labels program start events).length => rank start (labels program start events)[i.val]) := by
  intro a b equal
  have ma := List.getElem_mem a.isLt (l := labels program start events)
  have mb := List.getElem_mem b.isLt (l := labels program start events)
  have unique := labels_unique program start events
  have identityEq : identity (labels program start events)[a.val] = identity (labels program start events)[b.val] := by
    by_cases ta : (labels program start events)[a.val].thread = none <;>
      by_cases tb : (labels program start events)[b.val].thread = none
    · simp [rank,ta,tb] at equal
      simp [identity,ta,tb,equal]
    · have bound := initial_rank ma ta
      simp [rank,ta,tb] at equal bound
      omega
    · have bound := initial_rank mb tb
      simp [rank,ta,tb] at equal bound
      omega
    · have pos : (labels program start events)[a.val].position = (labels program start events)[b.val].position := by
        simpa [rank,ta,tb] using equal
      rw [program_same_position ma mb ta tb pos]
  have eq : a.val=b.val := by
    apply unique.eq_of_getElem_eq (by simp) (by simp)
    simpa using identityEq
  exact Fin.ext eq

/-- Chronological program events have increasing ranks regardless of thread. -/
theorem program_before (ta : a.thread ≠ none) (tb : b.thread ≠ none) (pos : a.position < b.position) :
    rank start a < rank start b := by simp [rank,ta,tb,pos]

theorem initial_iff (member : e ∈ labels program start events) :
    e.effect.op = .init ↔ e.thread = none := by
  by_cases thread : e.thread = none
  · obtain ⟨i,_,rfl⟩ := initial_origin member thread
    simp [Initial.occurrence]
  · obtain ⟨g,t,space,occ,eff,_,_,eq⟩ := program_origin member thread
    rw [eq]
    cases hk : eff.kind <;> simp [ofEffect,Access.effect,AccessKind.op,hk]

theorem no_release (member : e ∈ labels program start events) : e.effect.op ≠ .store .release := by
  by_cases thread : e.thread = none
  · rw [(initial_iff member).mpr thread]; decide
  · obtain ⟨g,t,space,occ,eff,_,_,eq⟩ := program_origin member thread
    rw [eq]
    cases hk : eff.kind <;> simp [ofEffect,Access.effect,AccessKind.op,hk]

theorem initial_position (member : e ∈ labels program start events) (thread : e.thread = none) :
    e.position=e.effect.address := by
  obtain ⟨i,_,rfl⟩ := initial_origin member thread
  rfl

theorem initial_before (program : List Instr) (start : Grid.State groups n) (events : List (Grid.Event groups n))
    (source co) (i w : Fin (labels program start events).length)
    (hi : (graph program start events source co).initial i)
    (same : (graph program start events source co).sameAddress i w) (ne : i≠w) :
    rank start ((graph program start events source co).event i) <
      rank start ((graph program start events source co).event w) := by
  have mi := List.getElem_mem i.isLt (l := labels program start events)
  have mw := List.getElem_mem w.isLt (l := labels program start events)
  have ti := (initial_iff mi).mp hi
  by_cases tw : ((graph program start events source co).event w).thread = none
  · have pi := initial_position mi ti
    have pw := initial_position mw tw
    have eq : rank start ((graph program start events source co).event i) =
        rank start ((graph program start events source co).event w) := by
      simp only [Graph.sameAddress] at same
      change (labels program start events)[i.val].effect.address =
        (labels program start events)[w.val].effect.address at same
      change (labels program start events)[w.val].thread = none at tw
      simp [graph,TraceMemory.graph,rank,ti,tw,pi,pw,same]
    exact False.elim (ne (rank_injective program start events eq))
  · have bound := initial_rank mi ti
    change rank start (labels program start events)[i.val] < _
    have wr : rank start ((graph program start events source co).event w) =
        ceiling start+((graph program start events source co).event w).position := by
      simp [rank,tw]
    rw [wr]
    omega

theorem base_before (program : List Instr) (start : Grid.State groups n) (events : List (Grid.Event groups n))
    (source co) (a b : Fin (labels program start events).length)
    (edge : Graph.Ordered.baseEdge (graph program start events source co) (cross program start events) a b) :
    rank start ((graph program start events source co).event a)<rank start ((graph program start events source co).event b) := by
  rcases edge with (po | sync) | edge
  · exact program_before po.1 (by rw [← po.2.1]; exact po.1) po.2.2
  · obtain ⟨_,w,r,release,_⟩ := sync
    have no := no_release (List.getElem_mem a.isLt (l := labels program start events))
    rcases release with ⟨_,rel⟩ | ⟨rel,_⟩ <;> exact False.elim (no rel)
  · have pos := cross_forward program start events a b edge
    obtain ⟨g,w,r,key,arrival,completion,_,_,_,ta,tb,_,_⟩ := edge
    exact program_before (by change (labels program start events)[a].thread≠none; rw [ta]; simp)
      (by change (labels program start events)[b].thread≠none; rw [tb]; simp) pos

end Ptx.Scalar.Parallel.Grid.Memory.Chronology

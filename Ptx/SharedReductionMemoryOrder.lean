import Ptx.SharedReductionMemory

/-! Source-independent order from actual keyed collective events. These facts do
not replace the separate reachable control/history proof that all required
producer stores and leader loads surround the completed phase. -/
namespace Ptx.Scalar.SharedReduction.Machine.Memory

open Ptx.TraceMemory

/-- Each endpoint belongs to its own arrival's participant. All indices are
positions in the same complete actual trace; completion has the same exact key. -/
def barrierOrder (trace : List (Event n)) (a b : Ptx.Occurrence) : Prop :=
  ∃ key, ∃ (ta tb : Fin n), ∃ ia ib done,
    a.thread = some ta.val ∧ b.thread = some tb.val ∧
    trace[ia]? = some (.barrier (.arrival key ta)) ∧
    trace[ib]? = some (.barrier (.arrival key tb)) ∧
    trace[done]? = some (.barrier (.completion key)) ∧
    a.position < ia ∧ ia < done ∧ ib < done ∧ done < b.position

/-- This is the extra relation supplied to the existing unclosed-causality model. -/
def extra (global shared : List Word) (trace : List (Event n))
    (source : Fin (labels global shared trace).length → Fin (labels global shared trace).length)
    (co : Fin (labels global shared trace).length → Fin (labels global shared trace).length → Bool)
    (a b : Fin (labels global shared trace).length) : Prop :=
  barrierOrder trace ((graph global shared trace source co).event a)
    ((graph global shared trace source co).event b)

theorem barrier_order_increases (trace : List (Event n)) (a b : Ptx.Occurrence)
    (order : barrierOrder trace a b) : a.position < b.position := by
  obtain ⟨key,ta,tb,ia,ib,done,_,_,_,_,_,first,second,_,last⟩ := order
  omega

theorem barrier_order_noninitial (trace : List (Event n)) (a b : Ptx.Occurrence)
    (order : barrierOrder trace a b) : a.thread ≠ none ∧ b.thread ≠ none := by
  obtain ⟨key,ta,tb,ia,ib,done,ha,hb,_⟩ := order
  simp [ha,hb]

theorem barrier_order_acyclic (trace : List (Event n)) (a : Ptx.Occurrence) :
    ¬Path (barrierOrder trace) a a := by
  intro cycle
  exact Nat.lt_irrefl _ (Path.rank_increases (fun e => e.position)
    (barrier_order_increases trace) cycle)

/-- An actual cross-barrier path contributes base order before the final
same-address restriction. It is never added directly as a transitive cause. -/
theorem barrier_base (global shared : List Word) (trace : List (Event n))
    (source co) (a b : Fin (labels global shared trace).length)
    (order : extra global shared trace source co a b) :
    Graph.Ordered.base (graph global shared trace source co)
      (extra global shared trace source co) a b := .edge (.inr order)

theorem barrier_cause (global shared : List Word) (trace : List (Event n))
    (source co) (a b : Fin (labels global shared trace).length)
    (order : extra global shared trace source co a b)
    (same : (graph global shared trace source co).sameAddress a b) :
    Graph.Ordered.cause (graph global shared trace source co)
      (extra global shared trace source co) a b :=
  .inl ⟨barrier_base global shared trace source co a b order,same⟩

/-- If an actual store precedes its own arrival and a read follows the same
completed phase, initialization cannot supply that read. This conclusion does
not assume different old/new values, or that this is the only program store. -/
theorem barrier_excludes_initial_source (global shared : List Word) (trace : List (Event n))
    (source co) (w r : Fin (labels global shared trace).length)
    (valid : Graph.Ordered.Valid (graph global shared trace source co)
      (extra global shared trace source co))
    (write : (graph global shared trace source co).write w)
    (read : (graph global shared trace source co).read r)
    (same : (graph global shared trace source co).sameAddress w r)
    (order : extra global shared trace source co w r) :
    ¬(graph global shared trace source co).initial ((graph global shared trace source co).source r) := by
  intro initialSource
  let g := graph global shared trace source co
  obtain ⟨sourceWrite,sourceAddress,_⟩ := valid.sources.compatible r read
  have cause := barrier_cause global shared trace source co w r order same
  have notInitialWrite : ¬g.initial w := by
    have notNone := (barrier_order_noninitial trace (g.event w) (g.event r) order).1
    intro initialWrite
    have member : g.event w ∈ labels global shared trace := List.getElem_mem _
    rcases labels_origin global shared trace _ member with ⟨i,hi,he⟩ | ⟨t,ht,p,hp,ha,he⟩
    · exact notNone (by simp [← he,Initial.occurrence])
    · have impossible : p.access.kind.op = .init := by
        simpa [Graph.initial,← he,Projected.occurrence,Access.effect] using initialWrite
      cases hk : p.access.kind <;> simp [AccessKind.op,hk] at impossible
  have different : g.source r ≠ w := by
    intro eq
    exact notInitialWrite (eq ▸ initialSource)
  have before : g.coherence (g.source r) w :=
    valid.co.initFirst _ _ initialSource write (sourceAddress.trans same.symm) different
  exact valid.no_stale w r write read same cause before

/-- A separate structural uniqueness proof completes source forcing. This helper
exposes that exact obligation; the reduction must prove it from its real runs. -/
theorem barrier_unique_source (global shared : List Word) (trace : List (Event n))
    (source co) (w r : Fin (labels global shared trace).length)
    (valid : Graph.Ordered.Valid (graph global shared trace source co)
      (extra global shared trace source co))
    (write : (graph global shared trace source co).write w)
    (read : (graph global shared trace source co).read r)
    (same : (graph global shared trace source co).sameAddress w r)
    (order : extra global shared trace source co w r)
    (unique : ∀ v, (graph global shared trace source co).write v →
      ¬(graph global shared trace source co).initial v →
      (graph global shared trace source co).sameAddress v r → v = w) :
    (graph global shared trace source co).source r = w ∧
      ((graph global shared trace source co).event r).effect.value =
      ((graph global shared trace source co).event w).effect.value := by
  have compatible := valid.sources.compatible r read
  have notInitial := barrier_excludes_initial_source global shared trace source co w r
    valid write read same order
  have sourceEq := unique _ compatible.1 notInitial compatible.2.1
  exact ⟨sourceEq,by simpa [sourceEq] using compatible.2.2.symm⟩

end Ptx.Scalar.SharedReduction.Machine.Memory

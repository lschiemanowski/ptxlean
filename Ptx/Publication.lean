import Ptx.Memory

/-!
Reusable consequences of the restricted whole-word memory rules. These proofs
do not enlarge Graph.Valid into a sufficient semantics for dependent PTX.
They neither create event labels nor assert that a candidate execution exists.
-/
namespace Ptx.Graph

/-- A directly observed release/acquire pair synchronizes when the two matching
accesses are issued by different threads in this all-GPU fragment. -/
theorem direct_sync (g : Graph n) (w r : Fin n)
    (different : (g.event w).thread ≠ (g.event r).thread)
    (released : g.release w) (acquired : g.acquire r)
    (source : g.source r = w) (same : g.sameAddress w r) : g.sync w r := by
  have hw : (g.event w).effect.op = .store .release := released
  have hr : (g.event r).effect.op = .load .acquire := acquired
  have strong : g.morallyStrong w r := by
    simp [morallyStrong, initial, hw, hr, same]
  exact ⟨different, w, r, Or.inl ⟨rfl, released⟩,
    Or.inl ⟨rfl, acquired⟩, ⟨⟨by simp [read, hr], source⟩, strong⟩, strong⟩

/-- Publication first constructs a path across addresses, then applies the
same-address restriction at its data endpoints. No closure of cause is added. -/
theorem publication_cause (g : Graph n) (dataWrite releaseWrite flagRead dataRead : Fin n)
    (before : g.po dataWrite releaseWrite) (after : g.po flagRead dataRead)
    (synchronizes : g.sync releaseWrite flagRead)
    (same : g.sameAddress dataWrite dataRead) : g.cause dataWrite dataRead := by
  exact Or.inl ⟨.join (.edge (Or.inl before))
    (.join (.edge (Or.inr synchronizes)) (.edge (Or.inl after))), same⟩

/-- A causally preceding write supplies the read if every other compatible
write is earlier in coherence. The premises concern writes and ordering, not
the desired output value. -/
theorem source_of_latest (g : Graph n) (valid : g.Valid) (w r : Fin n)
    (written : g.write w) (readAt : g.read r) (same : g.sameAddress w r)
    (ordered : g.cause w r)
    (latest : ∀ v, g.write v → g.sameAddress v r → v ≠ w → g.coherence v w) :
    g.source r = w := by
  by_cases h : g.source r = w
  · exact h
  · have compatible := valid.sources.compatible r readAt
    exact False.elim (valid.no_stale w r written readAt same ordered
      (latest (g.source r) compatible.1 compatible.2.1 h))

/-- Exact value agreement follows only after identifying the actual source. -/
theorem value_of_source (g : Graph n) (sources : g.Sources) (w r : Fin n)
    (readAt : g.read r) (source : g.source r = w) :
    (g.event r).effect.value = (g.event w).effect.value := by
  have h := (sources.compatible r readAt).2.2
  rw [source] at h
  exact h.symm

/-- A common special case has exactly two possible sources: the initial write
and one program write. Initialization is rejected using its coherence position. -/
theorem source_of_initial_or_write (g : Graph n) (valid : g.Valid) (i w r : Fin n)
    (initialized : g.initial i) (written : g.write w) (readAt : g.read r)
    (initialAddress : g.sameAddress i w) (different : i ≠ w)
    (same : g.sameAddress w r) (ordered : g.cause w r)
    (choices : g.source r = i ∨ g.source r = w) : g.source r = w := by
  rcases choices with hi | hw
  · have coherent := valid.co.initFirst i w initialized written initialAddress different
    exact False.elim (valid.no_stale w r written readAt same ordered (by
      rw [hi]
      exact coherent))
  · exact hw

end Ptx.Graph

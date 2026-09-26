import PtxBinary32.GridDenseOwnership
import PtxBinary32.GridGraphUnique

namespace Ptx.Scalar.Parallel.GridDense
open Ptx.Scalar.Parallel.Dense

theorem candidate_store_unique (s : Dense.Shape) (b : Bounds s) (global : List Word)
    (seeds : Fin s.threads → Scalar.State) {events : List (Grid.Event s.rows s.width)} {final : Grid.State s.rows s.width}
    (run : Grid.Runs (config s b) (program s) (initial s global seeds) events final)
    (p q : Nat) (g h : Fin s.rows) (t u : Fin s.width) (space seen : Space) (e f : Scalar.Occurrence) (a z : MemoryEffect)
    (hp : events[p]?=some (g,.scalar t (some space) e)) (hq : events[q]?=some (h,.scalar u (some seen) f))
    (he : e.memory=some a) (hf : f.memory=some z) (ha : a.kind=.store) (hz : z.kind=.store)
    (same : (Grid.location g space a.address).code=(Grid.location h seen z.address).code) : p=q := by
  cases space <;> cases seen
  · exact global_store_unique s b global seeds run p q g h t u e f a z hp hq he hf ha hz same
  · exact False.elim (Grid.global_shared_distinct g h _ _ same)
  · exact False.elim (Grid.global_shared_distinct h g _ _ same.symm)
  · exact shared_store_unique s b global seeds run p q g h t u e f a z hp hq he hf ha hz same

/-- The combined graph contains at most one actual noninitial writer per cell. -/
theorem graph_writer_unique (s : Dense.Shape) (b : Bounds s) (global : List Word)
    (seeds : Fin s.threads → Scalar.State) {events : List (Grid.Event s.rows s.width)} {final : Grid.State s.rows s.width}
    (run : Grid.Runs (config s b) (program s) (initial s global seeds) events final)
    (source co) (v w : Fin (Grid.Memory.labels (program s) (initial s global seeds) events).length)
    (hv : (Grid.Memory.graph (program s) (initial s global seeds) events source co).write v)
    (hw : (Grid.Memory.graph (program s) (initial s global seeds) events source co).write w)
    (nv : ¬(Grid.Memory.graph (program s) (initial s global seeds) events source co).initial v)
    (nw : ¬(Grid.Memory.graph (program s) (initial s global seeds) events source co).initial w)
    (same : (Grid.Memory.graph (program s) (initial s global seeds) events source co).sameAddress v w) : v=w := by
  obtain ⟨g,t,p,space,e,a,hp,_,_,he,ha,ve⟩ := Grid.Memory.program_write_origin (program s) (initial s global seeds) events source co v hv nv
  obtain ⟨h,u,q,seen,f,z,hq,_,_,hf,hz,we⟩ := Grid.Memory.program_write_origin (program s) (initial s global seeds) events source co w hw nw
  have location : (Grid.location g space a.address).code=(Grid.location h seen z.address).code := by
    simpa [Graph.sameAddress,ve,we,Ptx.TraceMemory.Access.effect,Grid.Memory.ofEffect] using same
  have position := candidate_store_unique s b global seeds run p q g h t u space seen e f a z hp hq he hf ha hz location
  have owners : g=h ∧ t=u := by
    rw [← position,hp] at hq
    have eq := Prod.mk.inj (Option.some.inj hq)
    exact ⟨eq.1,(Event.scalar.inj eq.2).1⟩
  have eq : Ptx.TraceMemory.identity ((Grid.Memory.graph (program s) (initial s global seeds) events source co).event v)=
      Ptx.TraceMemory.identity ((Grid.Memory.graph (program s) (initial s global seeds) events source co).event w) := by
    simp [ve,we,Ptx.TraceMemory.identity,position,owners.1,owners.2]
  apply Fin.ext
  apply (Grid.Memory.labels_unique (program s) (initial s global seeds) events).eq_of_getElem_eq (by simp) (by simp)
  simpa [Grid.Memory.graph,Ptx.TraceMemory.graph] using eq

end Ptx.Scalar.Parallel.GridDense

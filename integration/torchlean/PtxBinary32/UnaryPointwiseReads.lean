import PtxBinary32.UnaryPointwiseControl
import PtxBinary32.ParallelUnaryControl
import PtxBinary32.ParallelUnaryMemory

/-! In-place pointwise reads retain their original values under the existing
memory constraints: another lane cannot write the location, and the reader's
own later store cannot be its source. No chronological-load premise is used. -/
namespace Ptx.Scalar.UnaryPointwise
open ParallelUnary Ptx.TraceMemory

variable {n : Nat} {op : Op} {common : Nat} {before : List Word}
variable {seeds : Fin n→Scalar.State} {events : List (ParallelUnary.Event n)} {final : ParallelUnary.State n}

theorem straight (op : Op) : ParallelUnary.Straight (program op) := by
  intro i member
  cases op <;> simp [program,body,arithmetic,ownLoad,commonLoad,ownStore,exitInstr] at member
  all_goals repeat' (first | (rcases member with rfl | member) | (subst i))
  all_goals simp [ParallelUnary.StraightInstr,Scalar.Instr.plain]

theorem pointer_index (i : Nat) (fit : i<2^62) : (pointer i).toNat/4=i := by
  have bytes : 4*i<18446744073709551616 := by omega
  simp [pointer,SoftmaxMemory.address,BitVec.toNat_ofNat,Nat.mod_eq_of_lt bytes]

/-- Every program writer at a load's location is the same lane's later store.
The common operand has no writer in this launch. -/
theorem stores_follow_read
    (run : ParallelUnary.Runs target (program op) (initial common before seeds) events final)
    (separate : n≤common) (fit : common<2^62)
    (p q : Nat) (e f : ParallelUnary.Event n) (a b : MemoryEffect)
    (hp : events[p]?=some e) (hq : events[q]?=some f)
    (ha : e.memory=some a) (hb : f.memory=some b)
    (read : a.kind=.load) (write : b.kind=.store)
    (same : a.address.toNat/4=b.address.toNat/4) :
    e.thread=f.thread ∧ p<q := by
  have left := run_memory run (List.mem_of_getElem? hp) ha
  have right := run_memory run (List.mem_of_getElem? hq) hb
  have store : f.pc=storePC op ∧ b.address=pointer f.thread.val := by
    rcases right with h|h|h
    · simp [write] at h
    · simp [write] at h
    · exact ⟨h.1,h.2.2⟩
  have wf : f.thread.val<2^62 := lt_of_lt_of_le f.thread.isLt (le_trans separate fit.le)
  rw [store.2,pointer_index _ wf] at same
  rcases left with h|h|h
  · have rf : e.thread.val<2^62 := lt_of_lt_of_le e.thread.isLt (le_trans separate fit.le)
    rw [h.2.2,pointer_index _ rf] at same
    have thread : e.thread=f.thread := Fin.ext same
    refine ⟨thread,(ParallelUnary.position_iff_pc run (straight op) p q e f hp hq thread).mpr ?_⟩
    rw [h.1,store.1]
    cases op <;> decide
  · rw [h.2.2,pointer_index _ fit] at same
    have bound := f.thread.isLt
    omega
  · simp [read] at h

/-- Admission forces each actual read to the initial arena value, including
reads whose own location is overwritten later by the same lane. -/
theorem read_initial
    (run : ParallelUnary.Runs target (program op) (initial common before seeds) events final)
    (separate : n≤common) (fit : common<2^62) (source co)
    (valid : ParallelUnary.Memory.Admitted (program op) before events source co)
    (position : Nat) (thread : Fin n) (occ : Scalar.Occurrence) (effect : MemoryEffect)
    (atPos : events[position]?=some (.scalar thread occ))
    (memory : occ.memory=some effect) (read : effect.kind=.load) :
    effect.value=before[effect.address.toNat/4]! := by
  obtain ⟨r,label⟩ := ParallelUnary.Memory.run_graph_complete run source co position thread occ effect atPos memory
  change (ParallelUnary.Memory.graph (program op) before events source co).event r=_ at label
  let g := ParallelUnary.Memory.graph (program op) before events source co
  have isRead : g.read r := by
    simp [g,Graph.read,label,ParallelUnary.Memory.ofEffect,Parallel.Memory.ofEffect,Access.effect,AccessKind.op,read]
  have address : (g.event r).effect.address=(⟨0,effect.address.toNat/4⟩ : Location 2).code := by
    simp [g,label,ParallelUnary.Memory.ofEffect,Parallel.Memory.ofEffect,Access.effect,Parallel.Memory.location,Parallel.Memory.slot]
  have future : ∀w, g.write w → ¬g.initial w → g.sameAddress w r →
      Graph.Ordered.cause g (fun _ _=>False) r w := by
    intro w write noninitial same
    obtain ⟨u,q,other,stored,atQ,_,_,mem,kind,otherLabel⟩ :=
      ParallelUnary.Memory.program_write_origin (program op) before events source co w write noninitial
    have location : effect.address.toNat/4=stored.address.toNat/4 := by
      change (g.event w).effect.address=(g.event r).effect.address at same
      change (ParallelUnary.Memory.graph (program op) before events source co).event w=_ at otherLabel
      rw [otherLabel,label] at same
      simpa [ParallelUnary.Memory.ofEffect,Parallel.Memory.ofEffect,Access.effect,Parallel.Memory.location,
        Parallel.Memory.slot,Location.code] using same.symm
    have ordered := stores_follow_read run separate fit position q (.scalar thread occ) (.scalar u other)
      effect stored atPos atQ memory mem read kind location
    have po : g.po r w := by
      simp [g,Graph.po,label,otherLabel,show thread=u from ordered.1,ordered.2]
    exact Or.inl ⟨Path.edge (Or.inl (Or.inl po)),same.symm⟩
  have value := ParallelUnary.Memory.initial_read_value (program op) before events source co valid r
    (effect.address.toNat/4) isRead address future
  simpa [g,label,ParallelUnary.Memory.ofEffect,Parallel.Memory.ofEffect,Access.effect] using value

/-- A convenient all-occurrences form for the register data invariant. -/
theorem reads_initial
    (run : ParallelUnary.Runs target (program op) (initial common before seeds) events final)
    (separate : n≤common) (fit : common<2^62) (source co)
    (valid : ParallelUnary.Memory.Admitted (program op) before events source co)
    (event : ParallelUnary.Event n) (effect : MemoryEffect) (member : event∈events)
    (memory : event.memory=some effect) (read : effect.kind=.load) :
    effect.value=before[effect.address.toNat/4]! := by
  cases event with
  | scalar thread occ =>
    obtain ⟨position,hp,atPos⟩ := List.mem_iff_getElem.mp member
    exact read_initial run separate fit source co valid position thread occ effect
      (List.getElem?_eq_some_iff.mpr ⟨hp,atPos⟩) memory read
  | binary _ _ | exponential _ _ | reciprocal _ _ => simp [ParallelUnary.Event.memory] at memory

end Ptx.Scalar.UnaryPointwise

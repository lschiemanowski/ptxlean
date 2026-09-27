import PtxBinary32.MaximumProgram
import PtxBinary32.ParallelCompletion
import PtxBinary32.ParallelMemory

/-! Control-order consequences for every candidate parallel maximum trace, with
arbitrary schedules and load candidates. These do
not assume memory admission and do not yet prove computed-address ownership. -/
namespace Ptx.Scalar.Parallel.Maximum

/-- Every fetched instruction advances its lane or participates in a barrier;
no instruction branches or changes another lane's instruction pointer. -/
theorem program_straight (d : Nat) : Control.Straight (program d) := by
  intro i member
  simp only [program,List.mem_append,List.mem_flatMap,List.mem_range] at member
  rcases member with (first | ⟨k,hk,roundMem⟩) | last
  · simp [publish,publishCode,Dense.pointer] at first
    rcases first with rfl | rfl | rfl | rfl | rfl | rfl <;> trivial
  · simp [round,roundCode,roundPrefix,roundSuffix,Scalar.MaximumSelect.code,Dense.pointer] at roundMem
    rcases roundMem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> trivial
  · simp [output,outputCode,Dense.pointer] at last
    rcases last with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> trivial

/-- Distinct occurrences of one thread's scalar instructions cannot share a PC,
including memory stores. No unique-writer or read-value premise is needed. -/
theorem scalar_site_unique (d : Nat) {cfg : Config (width d)} {start final : Parallel.State (width d)}
    {events : List (Event (width d))} (run : Runs cfg (program d) start events final)
    (p q : Nat) (t : Fin (width d)) (space otherSpace : Option Space)
    (e f : Scalar.Occurrence)
    (hp : events[p]? = some (.scalar t space e))
    (hq : events[q]? = some (.scalar t otherSpace f)) (same : e.pc=f.pc) : p=q :=
  Control.same_site_unique run (program_straight d) p q _ _ t e.pc hp hq rfl (by simp [Control.stamp,same])

/-- An observed earlier-site memory instruction precedes the same thread's
actual barrier arrival, regardless of how the other threads were scheduled. -/
theorem scalar_before_arrival (d : Nat) {cfg : Config (width d)} {start final : Parallel.State (width d)}
    {events : List (Event (width d))} (run : Runs cfg (program d) start events final)
    (p a : Nat) (t : Fin (width d)) (space : Option Space) (e : Scalar.Occurrence) (key : Barrier.Key)
    (hp : events[p]? = some (.scalar t space e))
    (ha : events[a]? = some (.barrier (.arrival key t))) (before : e.pc<key.site) : p<a :=
  (Control.position_iff_pc run (program_straight d) p a _ _ t e.pc key.site hp ha rfl rfl).mpr before

/-- The consumer position is derived from its instruction site and an actual
completion, rather than supplied as a timing premise. -/
theorem scalar_after_completion (d : Nat) {cfg : Config (width d)} {start final : Parallel.State (width d)}
    {events : List (Event (width d))} (run : Runs cfg (program d) start events final)
    (aligned : Aligned start) (c p : Nat) (t : Fin (width d)) (space : Option Space)
    (e : Scalar.Occurrence) (key : Barrier.Key)
    (hc : events[c]? = some (.barrier (.completion key)))
    (hp : events[p]? = some (.scalar t space e)) (later : key.site<e.pc) : c<p :=
  Control.site_after_completion run (program_straight d) aligned c p key _ t e.pc hc hp rfl later

private theorem publish_store_site (d : Nat) (pc : Nat) (space : Space) (i : Scalar.Instr)
    (fetch : (publish)[pc]? = some (.memory space i))
    (store : Memory.Prior.memoryKind i.op = some .store) : pc=4 ∧ space=.shared := by
  have bound : pc<6 := by simpa using (List.getElem?_eq_some_iff.mp fetch).choose
  interval_cases pc <;> simp_all [publish,publishCode,Dense.pointer,Memory.Prior.memoryKind,
    Ptx.Scalar.SharedReduction.Machine.Control.memoryKind,Scalar.Instr.plain]
  all_goals obtain ⟨rfl,rfl⟩ := fetch
  all_goals simp_all [Memory.Prior.memoryKind]

private theorem round_store_site (d : Nat) (k pc : Nat) (space : Space) (i : Scalar.Instr)
    (fetch : (round d k)[pc]? = some (.memory space i))
    (store : Memory.Prior.memoryKind i.op = some .store) : pc=22 ∧ space=.shared := by
  have bound : pc<24 := by simpa using (List.getElem?_eq_some_iff.mp fetch).choose
  interval_cases pc <;> simp_all [round,roundCode,roundPrefix,roundSuffix,Scalar.MaximumSelect.code,Dense.pointer,scalar,guarded,Memory.Prior.memoryKind,
    Ptx.Scalar.SharedReduction.Machine.Control.memoryKind,Scalar.Instr.plain]
  all_goals obtain ⟨rfl,rfl⟩ := fetch
  all_goals simp_all [Memory.Prior.memoryKind]

private theorem output_store_site (d : Nat) (pc : Nat) (space : Space) (i : Scalar.Instr)
    (fetch : (output d)[pc]? = some (.memory space i))
    (store : Memory.Prior.memoryKind i.op = some .store) : pc=10 ∧ space=.global := by
  have bound : pc<12 := by simpa using (List.getElem?_eq_some_iff.mp fetch).choose
  interval_cases pc <;> simp_all [output,outputCode,Dense.pointer,scalar,guarded,Memory.Prior.memoryKind,
    Ptx.Scalar.SharedReduction.Machine.Control.memoryKind]
  all_goals obtain ⟨rfl,rfl⟩ := fetch
  all_goals simp_all [Memory.Prior.memoryKind]

/-- Exhaustive store-site classification of the actual instruction list. -/
theorem fetched_store_site (d : Nat) (pc : Nat) (space : Space) (i : Scalar.Instr)
    (fetch : (program d)[pc]? = some (.memory space i))
    (store : Memory.Prior.memoryKind i.op = some .store) :
    (pc=4 ∧ space=.shared) ∨
    (∃ k, k<d ∧ pc=6+24*k+22 ∧ space=.shared) ∨
    (pc=6+24*d+10 ∧ space=.global) := by
  have bound : pc<18+24*d := by simpa [program_length] using (List.getElem?_eq_some_iff.mp fetch).choose
  by_cases publication : pc<6
  · left
    apply publish_store_site d pc space i _ store
    simpa [program,List.getElem?_append,publication,show pc<6+24*d by omega,
      List.length_flatMap,List.sum_replicate,Nat.mul_comm] using fetch
  · by_cases rounds : pc<6+24*d
    · let k := (pc-6)/24
      let j := (pc-6)%24
      have kj : 6+24*k+j=pc := by dsimp [k,j]; omega
      have hk : k<d := by dsimp [k]; omega
      have hj : j<(round d k).length := by rw [round_length]; dsimp [j]; omega
      have atJ : (round d k)[j]? = some (.memory space i) := by
        rw [← round_fetch d k hk j hj,kj]; exact fetch
      obtain ⟨siteEq,which⟩ := round_store_site d k j space i atJ store
      exact .inr (.inl ⟨k,hk,by omega,which⟩)
    · have jbound : pc-(6+24*d)<(output d).length := by rw [output_length]; omega
      have atJ : (output d)[pc-(6+24*d)]? = some (.memory space i) := by
        rw [← output_fetch d (pc-(6+24*d)) jbound,show 6+24*d+(pc-(6+24*d))=pc by omega]
        exact fetch
      obtain ⟨siteEq,which⟩ := output_store_site d _ space i atJ store
      exact .inr (.inr ⟨by omega,which⟩)

/-- Every emitted store, including in incomplete candidate runs, comes from one
of the classified sites. This is stronger than inspecting the selected runner. -/
theorem trace_store_site (d : Nat) {cfg : Config (width d)} {start final : Parallel.State (width d)}
    {events : List (Event (width d))} (run : Runs cfg (program d) start events final)
    (t : Fin (width d)) (space : Space) (occ : Scalar.Occurrence) (effect : MemoryEffect)
    (member : .scalar t (some space) occ ∈ events) (memory : occ.memory=some effect)
    (store : effect.kind=.store) :
    (occ.pc=4 ∧ space=.shared) ∨
    (∃ k, k<d ∧ occ.pc=6+24*k+22 ∧ space=.shared) ∨
    (occ.pc=6+24*d+10 ∧ space=.global) := by
  have access := Memory.run_access_complete run member memory
  have conditions : (program d)[occ.pc]? = some (.memory space occ.instruction) ∧
      occ.executed=true ∧ Memory.Prior.memoryKind occ.instruction.op=some effect.kind := by
    simpa [Memory.access,memory] using access
  exact fetched_store_site d occ.pc space occ.instruction conditions.1 (by simpa [store] using conditions.2.2)

end Ptx.Scalar.Parallel.Maximum

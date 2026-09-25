import PtxBinary32.DenseProgram
import PtxBinary32.ParallelCompletion
import PtxBinary32.DenseRounds
import PtxBinary32.DenseOutput
import PtxBinary32.ParallelMemory

/-! Control-order consequences for every candidate dense forward trace, with
arbitrary schedules, load candidates and permitted binary32 results. These do
not assume memory admission and do not yet prove computed-address ownership. -/
namespace Ptx.Scalar.Parallel.Dense

/-- This property is checked against every instruction in the supplied list. -/
theorem program_straight (s : Shape) : Control.Straight (program s) := by
  intro i member
  simp only [program,List.mem_append,List.mem_flatMap,List.mem_range] at member
  rcases member with (first | ⟨k,hk,roundMem⟩) | last
  · simp [products,pointer] at first
    rcases first with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals trivial
  · simp [round,pointer] at roundMem
    rcases roundMem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals trivial
  · simp [output,pointer] at last
    rcases last with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals trivial

/-- Distinct occurrences of one thread's scalar instructions cannot share a PC,
including memory stores. No unique-writer or read-value premise is needed. -/
theorem scalar_site_unique (s : Shape) {cfg : Config s.threads} {start final : Parallel.State s.threads}
    {events : List (Event s.threads)} (run : Runs cfg (program s) start events final)
    (p q : Nat) (t : Fin s.threads) (space otherSpace : Option Space)
    (e f : Scalar.Occurrence)
    (hp : events[p]? = some (.scalar t space e))
    (hq : events[q]? = some (.scalar t otherSpace f)) (same : e.pc=f.pc) : p=q :=
  Control.same_site_unique run (program_straight s) p q _ _ t e.pc hp hq rfl (by simp [Control.stamp,same])

/-- An observed earlier-site memory instruction precedes the same thread's
actual barrier arrival, regardless of how the other threads were scheduled. -/
theorem scalar_before_arrival (s : Shape) {cfg : Config s.threads} {start final : Parallel.State s.threads}
    {events : List (Event s.threads)} (run : Runs cfg (program s) start events final)
    (p a : Nat) (t : Fin s.threads) (space : Option Space) (e : Scalar.Occurrence) (key : Barrier.Key)
    (hp : events[p]? = some (.scalar t space e))
    (ha : events[a]? = some (.barrier (.arrival key t))) (before : e.pc<key.site) : p<a :=
  (Control.position_iff_pc run (program_straight s) p a _ _ t e.pc key.site hp ha rfl rfl).mpr before

/-- The consumer position is derived from its instruction site and an actual
completion, rather than supplied as a timing premise. -/
theorem scalar_after_completion (s : Shape) {cfg : Config s.threads} {start final : Parallel.State s.threads}
    {events : List (Event s.threads)} (run : Runs cfg (program s) start events final)
    (aligned : Aligned start) (c p : Nat) (t : Fin s.threads) (space : Option Space)
    (e : Scalar.Occurrence) (key : Barrier.Key)
    (hc : events[c]? = some (.barrier (.completion key)))
    (hp : events[p]? = some (.scalar t space e)) (later : key.site<e.pc) : c<p :=
  Control.site_after_completion run (program_straight s) aligned c p key _ t e.pc hc hp rfl later

private theorem products_store_site (s : Shape) (pc : Nat) (space : Space) (i : Scalar.Instr)
    (fetch : (products s)[pc]? = some (.memory space i))
    (store : Memory.Prior.memoryKind i.op = some .store) : pc=20 ∧ space=.shared := by
  have bound : pc<22 := by simpa using (List.getElem?_eq_some_iff.mp fetch).choose
  interval_cases pc <;> simp_all [products,pointer,scalar,guarded,Memory.Prior.memoryKind,
    Ptx.Scalar.SharedReduction.Machine.Control.memoryKind,Scalar.Instr.plain]
  all_goals obtain ⟨_,rfl⟩ := fetch; contradiction

private theorem round_store_site (s : Shape) (k pc : Nat) (space : Space) (i : Scalar.Instr)
    (fetch : (round s k)[pc]? = some (.memory space i))
    (store : Memory.Prior.memoryKind i.op = some .store) : pc=14 ∧ space=.shared := by
  have bound : pc<16 := by simpa using (List.getElem?_eq_some_iff.mp fetch).choose
  interval_cases pc <;> simp_all [round,pointer,scalar,guarded,Memory.Prior.memoryKind,
    Ptx.Scalar.SharedReduction.Machine.Control.memoryKind,Scalar.Instr.plain]
  all_goals obtain ⟨_,rfl⟩ := fetch; contradiction

private theorem output_store_site (s : Shape) (pc : Nat) (space : Space) (i : Scalar.Instr)
    (fetch : (output s)[pc]? = some (.memory space i))
    (store : Memory.Prior.memoryKind i.op = some .store) : pc=18 ∧ space=.global := by
  have bound : pc<20 := by simpa using (List.getElem?_eq_some_iff.mp fetch).choose
  interval_cases pc <;> simp_all [output,pointer,scalar,guarded,Memory.Prior.memoryKind,
    Ptx.Scalar.SharedReduction.Machine.Control.memoryKind,Scalar.Instr.plain]
  all_goals obtain ⟨_,rfl⟩ := fetch; contradiction

/-- Exhaustive store-site classification of the actual instruction list. -/
theorem fetched_store_site (s : Shape) (pc : Nat) (space : Space) (i : Scalar.Instr)
    (fetch : (program s)[pc]? = some (.memory space i))
    (store : Memory.Prior.memoryKind i.op = some .store) :
    (pc=20 ∧ space=.shared) ∨
    (∃ k, k<s.depth ∧ pc=22+16*k+14 ∧ space=.shared) ∨
    (pc=22+16*s.depth+18 ∧ space=.global) := by
  have bound : pc<42+16*s.depth := by simpa [program_length] using (List.getElem?_eq_some_iff.mp fetch).choose
  by_cases product : pc<22
  · left
    apply products_store_site s pc space i _ store
    simpa [program,List.getElem?_append,product,show pc<22+16*s.depth by omega,
      List.length_flatMap,List.sum_replicate,Nat.mul_comm] using fetch
  · by_cases rounds : pc<22+16*s.depth
    · let k := (pc-22)/16
      let j := (pc-22)%16
      have kj : 22+16*k+j=pc := by dsimp [k,j]; omega
      have hk : k<s.depth := by dsimp [k]; omega
      have hj : j<(round s k).length := by rw [round_length]; dsimp [j]; omega
      have atJ : (round s k)[j]? = some (.memory space i) := by
        rw [← round_fetch s k hk j hj,kj]; exact fetch
      obtain ⟨siteEq,which⟩ := round_store_site s k j space i atJ store
      exact .inr (.inl ⟨k,hk,by omega,which⟩)
    · have jbound : pc-(22+16*s.depth)<(output s).length := by rw [output_length]; omega
      have atJ : (output s)[pc-(22+16*s.depth)]? = some (.memory space i) := by
        rw [← output_fetch s (pc-(22+16*s.depth)) jbound,show 22+16*s.depth+(pc-(22+16*s.depth))=pc by omega]
        exact fetch
      obtain ⟨siteEq,which⟩ := output_store_site s _ space i atJ store
      exact .inr (.inr ⟨by omega,which⟩)

/-- Every emitted store, including in incomplete candidate runs, comes from one
of the classified sites. This is stronger than inspecting the selected runner. -/
theorem trace_store_site (s : Shape) {cfg : Config s.threads} {start final : Parallel.State s.threads}
    {events : List (Event s.threads)} (run : Runs cfg (program s) start events final)
    (t : Fin s.threads) (space : Space) (occ : Scalar.Occurrence) (effect : MemoryEffect)
    (member : .scalar t (some space) occ ∈ events) (memory : occ.memory=some effect)
    (store : effect.kind=.store) :
    (occ.pc=20 ∧ space=.shared) ∨
    (∃ k, k<s.depth ∧ occ.pc=22+16*k+14 ∧ space=.shared) ∨
    (occ.pc=22+16*s.depth+18 ∧ space=.global) := by
  have access := Memory.run_access_complete run member memory
  have conditions : (program s)[occ.pc]? = some (.memory space occ.instruction) ∧
      occ.executed=true ∧ Memory.Prior.memoryKind occ.instruction.op=some effect.kind := by
    simpa [Memory.access,memory] using access
  exact fetched_store_site s occ.pc space occ.instruction conditions.1 (by simpa [store] using conditions.2.2)

end Ptx.Scalar.Parallel.Dense

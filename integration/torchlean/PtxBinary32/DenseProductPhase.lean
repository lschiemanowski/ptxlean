import PtxBinary32.DenseProducts

/-! A finite fetched execution of every product lane and the first actual
full-group barrier. This is a prefix of the dense kernel, not its completion
or an admission theorem for its memory graph. -/
namespace Ptx.Scalar.Parallel.Dense

/-- Earlier lanes have stored their product and wait at the barrier; later
lanes remain at entry. Both allocated arrays retain their lengths. -/
structure ProductInvariant (s : Shape) (original current : Parallel.State s.threads)
    (count : Nat) : Prop where
  global : current.global = original.global
  shared : current.shared.length = original.shared.length
  products : ∀ t : Fin s.threads, t.val < count → current.shared[t.val]? =
    some (nodeValue s original.global (t.val/s.width) 0 (t.val%s.width))
  pc : ∀ t : Fin s.threads, (current.lanes t).scalar.pc = if t.val < count then 21 else 0
  live : ∀ t, (current.lanes t).halted = false
  ids : ∀ t, (current.lanes t).scalar.regs 0 = BitVec.ofNat 32 t.val
  barrier : current.barrier = Barrier.reset 0
  site : current.site = none
  coordinates : ∀ t : Fin s.threads, t.val < count →
    (current.lanes t).scalar.regs 1 = BitVec.ofNat 32 (t.val%s.width) ∧
    (current.lanes t).scalar.regs 2 = BitVec.ofNat 32 (t.val/s.width)

theorem product_invariant_step (s : Shape) (b : Bounds s)
    (original current : Parallel.State s.threads) (count : Nat) (bound : count < s.threads)
    (invariant : ProductInvariant s original current count)
    (global : s.globalWords ≤ original.global.length) (shared : s.sharedWords ≤ original.shared.length) :
    ProductInvariant s original (productFinish s b current ⟨count,bound⟩) (count+1) := by
  let t : Fin s.threads := ⟨count,bound⟩
  have gs : s.globalWords ≤ current.global.length := by simpa [invariant.global] using global
  have ss : s.sharedWords ≤ current.shared.length := by rw [invariant.shared]; exact shared
  have memory := product_memory s b current t ss
  have control := product_control s b current t ss
  obtain ⟨events,segment⟩ := product_segment s b current t (invariant.ids t) gs ss
  have frame := segment.frame
  have pc0 : (current.lanes t).scalar.pc = 0 := by simp [invariant.pc,t]
  have pc21 : ((productFinish s b current t).lanes t).scalar.pc = 21 := by
    simpa [pc0] using frame.1
  refine ⟨memory.1.trans invariant.global,?_,?_,?_,?_,?_,control.1.trans invariant.barrier,
    control.2.1.trans invariant.site,?_⟩
  · rw [memory.2,List.length_set]; exact invariant.shared
  · intro u hu
    rw [memory.2]
    by_cases eq : u=t
    · subst u
      have inside : t.val < current.shared.length := by
        have mono : s.threads ≤ s.sharedWords := by
          change s.threads ≤ (s.depth+1)*s.threads
          nlinarith
        omega
      simp [inside,invariant.global]
    · have ne : t.val ≠ u.val := by intro h; exact eq (Fin.ext h.symm)
      rw [List.getElem?_set_ne ne]
      exact invariant.products u (by dsimp [t] at ne; omega)
  · intro u
    by_cases eq : u=t
    · subst u; simpa [t] using pc21
    · rw [control.2.2.2 u eq,invariant.pc]
      have ne : u.val ≠ count := by intro h; exact eq (Fin.ext h)
      change (if u.val<count then 21 else 0) = (if u.val<count+1 then 21 else 0)
      have same : u.val<count+1 ↔ u.val<count := by omega
      simp only [same]
  · intro u
    by_cases eq : u=t
    · subst u; exact frame.2.1.trans (invariant.live t)
    · rw [control.2.2.2 u eq]; exact invariant.live u
  · intro u
    by_cases eq : u=t
    · subst u; exact control.2.2.1.trans (invariant.ids t)
    · rw [control.2.2.2 u eq]; exact invariant.ids u

  · intro u hu
    by_cases eq : u=t
    · subst u; exact product_coordinates s b current t ss
    · rw [control.2.2.2 u eq]
      apply invariant.coordinates u
      have ne : u.val ≠ count := by intro h; exact eq (Fin.ext h)
      omega

/-- There is a concrete instruction execution of every product followed by
all barrier arrivals. The witness is selected; other admitted observations
require the separate memory-order argument. -/
theorem product_phase_exists (s : Shape) (b : Bounds s) (global shared : List Word)
    (seeds : Fin s.threads → Scalar.State)
    (globalBound : s.globalWords ≤ global.length) (sharedBound : s.sharedWords ≤ shared.length) :
    ∃ events final, ConcreteRuns (config s b) (program s) (initial s global shared seeds) events final ∧
      final.global = global ∧ final.shared.length = shared.length ∧
      (∀ t : Fin s.threads, final.shared[t.val]? =
        some (nodeValue s global (t.val/s.width) 0 (t.val%s.width))) ∧
      (∀ t, (final.lanes t).scalar.pc = 22 ∧ (final.lanes t).halted = false) ∧
      final.barrier = Barrier.reset 1 ∧ final.site = none ∧
      (∀ event ∈ events, AccessSafe (initial s global shared seeds) event) ∧
      (∀ t, (final.lanes t).scalar.regs 0 = BitVec.ofNat 32 t.val ∧
        (final.lanes t).scalar.regs 1 = BitVec.ofNat 32 (t.val%s.width) ∧
        (final.lanes t).scalar.regs 2 = BitVec.ofNat 32 (t.val/s.width)) := by
  let start := initial s global shared seeds
  have prefixRun : ∀ count, count ≤ s.threads → ∃ events current,
      ConcreteRuns (config s b) (program s) start events current ∧ ProductInvariant s start current count := by
    intro count bound
    induction count with
    | zero =>
      refine ⟨[],start,ConcreteRuns.nil,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
      · rfl
      · rfl
      · intro t ht; omega
      · intro t; simp [start,initial]
      · intro t; rfl
      · intro t; simp [start,initial,Scalar.update]
      · rfl
      · rfl
      · intro t ht; omega
    | succ count ih =>
      obtain ⟨events,current,run,inv⟩ := ih (by omega)
      let t : Fin s.threads := ⟨count,by omega⟩
      have gs : s.globalWords ≤ current.global.length := by rw [inv.global]; exact globalBound
      have ss : s.sharedWords ≤ current.shared.length := by rw [inv.shared]; exact sharedBound
      obtain ⟨next,step⟩ := product_run s b current t (inv.ids t) (by simp [inv.pc,t])
        (inv.live t) (by simp [inv.barrier,Barrier.reset]) gs ss
      exact ⟨events++next,_,concrete_runs_append run step,
        product_invariant_step s b start current count (by omega) inv globalBound sharedBound⟩
  obtain ⟨events,current,run,inv⟩ := prefixRun s.threads (Nat.le_refl _)
  have pcs : ∀ t, (current.lanes t).scalar.pc = 21 := by intro t; simp [inv.pc,t.isLt]
  have fetch : (program s)[21]? = some (.sync 0) := by simp [program,products,pointer]
  obtain ⟨arrivals,release⟩ := barrier_round_concrete (config s b) current (program s) 21 0
    pcs inv.live inv.barrier inv.site fetch (by change 94=94 ∧ 70≤70; decide)
  refine ⟨events++arrivals,afterRound current 0,concrete_runs_append run release,inv.global,inv.shared,?_,?_,rfl,rfl,?_,?_⟩
  · intro t; exact inv.products t t.isLt
  · intro t; exact ⟨by simp [afterRound,pcs],inv.live t⟩
  · intro event member; exact runs_access_safe (concrete_runs_append run release).toRuns event member
  · intro t; exact ⟨inv.ids t,inv.coordinates t t.isLt⟩

end Ptx.Scalar.Parallel.Dense

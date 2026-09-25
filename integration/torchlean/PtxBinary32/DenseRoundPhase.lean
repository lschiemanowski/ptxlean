import PtxBinary32.DenseProductPhase
import PtxBinary32.DenseRounds

namespace Ptx.Scalar.Parallel.Dense

/-- The control and data available immediately after a completed barrier. -/
structure PlaneReady (s : Shape) (inputs : List Word) (state : Parallel.State s.threads) (k : Nat) : Prop where
  global : state.global = inputs
  extent : s.sharedWords ≤ state.shared.length
  pc : ∀ t, (state.lanes t).scalar.pc = 22+16*k
  live : ∀ t, (state.lanes t).halted = false
  regs : ∀ t, (state.lanes t).scalar.regs 0 = BitVec.ofNat 32 t.val ∧
    (state.lanes t).scalar.regs 1 = BitVec.ofNat 32 (t.val%s.width) ∧
    (state.lanes t).scalar.regs 2 = BitVec.ofNat 32 (t.val/s.width)
  barrier : state.barrier = Barrier.reset (k+1)
  site : state.site = none
  values : ∀ r c, r < s.rows → c < 2^(s.depth-k) →
    state.shared[s.scratch k r c]? = some (nodeValue s inputs r k c)

theorem thread_coordinates (s : Shape) (r c : Nat) (hc : c < s.width) :
    s.thread r c / s.width = r ∧ s.thread r c % s.width = c := by
  have positive := width_positive s
  simp [Shape.thread,Nat.add_div,Nat.div_eq_of_lt hc,Nat.mod_eq_of_lt hc,Nat.not_le.mpr hc,positive]

/-- A sweep preserves every earlier plane while filling the fresh plane. -/
structure RoundInvariant (s : Shape) (start state : Parallel.State s.threads) (k count : Nat) : Prop where
  global : state.global = start.global
  length : state.shared.length = start.shared.length
  old : ∀ i, i < (k+1)*s.threads → state.shared[i]? = start.shared[i]?
  written : ∀ t : Fin s.threads, t.val < count → t.val%s.width < 2^(s.depth-(k+1)) →
    state.shared[nextIndex s k t]? = some (nodeValue s start.global (t.val/s.width) (k+1) (t.val%s.width))
  pc : ∀ t, (state.lanes t).scalar.pc = 22+16*k+(if t.val<count then 15 else 0)
  live : ∀ t, (state.lanes t).halted = false
  regs : ∀ t, (state.lanes t).scalar.regs 0 = (start.lanes t).scalar.regs 0 ∧
    (state.lanes t).scalar.regs 1 = (start.lanes t).scalar.regs 1 ∧
    (state.lanes t).scalar.regs 2 = (start.lanes t).scalar.regs 2
  barrier : state.barrier = start.barrier
  site : state.site = start.site

theorem round_reads (s : Shape) (k : Nat) (hk : k<s.depth) (global : List Word)
    (start state : Parallel.State s.threads) (ready : PlaneReady s global start k)
    (old : ∀ i, i < (k+1)*s.threads → state.shared[i]? = start.shared[i]?)
    (t : Fin s.threads) (active : t.val%s.width < 2^(s.depth-(k+1))) :
    state.shared[leftIndex s k t]! = nodeValue s global (t.val/s.width) k (2*(t.val%s.width)) ∧
    state.shared[leftIndex s k t+1]! = nodeValue s global (t.val/s.width) k (2*(t.val%s.width)+1) := by
  obtain ⟨hr,hc,ht⟩ := coordinates s t
  obtain ⟨left,right⟩ := children_bound s k (t.val%s.width) hk active
  have width : 2^(s.depth-k) ≤ s.width := Nat.pow_le_pow_right (by decide) (Nat.sub_le _ _)
  have li := thread_bound s (t.val/s.width) (2*(t.val%s.width)) hr (by omega)
  have ri := thread_bound s (t.val/s.width) (2*(t.val%s.width)+1) hr (by omega)
  have leq : leftIndex s k t = s.scratch k (t.val/s.width) (2*(t.val%s.width)) := by
    simp only [Shape.thread] at ht
    dsimp [leftIndex,Shape.scratch,Shape.thread]; omega
  have req : leftIndex s k t+1 = s.scratch k (t.val/s.width) (2*(t.val%s.width)+1) := by
    rw [leq]; simp [Shape.scratch,Shape.thread,Nat.add_assoc]
  have lb : leftIndex s k t < (k+1)*s.threads := by
    rw [leq]; simp only [Shape.scratch,Nat.add_mul]; omega
  have rb : leftIndex s k t+1 < (k+1)*s.threads := by
    rw [req]; simp only [Shape.scratch,Nat.add_mul]; omega
  constructor
  · rw [List.getElem!_eq_getElem?_getD,old _ lb,leq,ready.values _ _ hr left]; rfl
  · rw [List.getElem!_eq_getElem?_getD,old _ rb,req,ready.values _ _ hr right]; rfl

theorem round_invariant_step (s : Shape) (b : Bounds s) (k : Nat) (hk : k<s.depth)
    (global : List Word) (start state : Parallel.State s.threads) (ready : PlaneReady s global start k)
    (count : Nat) (bound : count<s.threads) (inv : RoundInvariant s start state k count) :
    RoundInvariant s start (roundFinish s b k state ⟨count,bound⟩) k (count+1) := by
  let t : Fin s.threads := ⟨count,bound⟩
  have tid := (inv.regs t).1.trans (ready.regs t).1
  have col := (inv.regs t).2.1.trans (ready.regs t).2.1
  have extent : s.sharedWords ≤ state.shared.length := by rw [inv.length]; exact ready.extent
  have eff := round_effect s b k hk state t tid col extent
  have frame := (segmentReference_sound (round_regular s b k hk state t tid col extent)).frame
  change ((roundFinish s b k state t).lanes t).scalar.pc = _ ∧
    ((roundFinish s b k state t).lanes t).halted = _ ∧ (roundFinish s b k state t).barrier = _ at frame
  have pc0 : (state.lanes t).scalar.pc = 22+16*k := by simp [inv.pc,t]
  have pc15 : ((roundFinish s b k state t).lanes t).scalar.pc = 22+16*k+15 := by simpa [pc0] using frame.1
  have others := eff.2.2.2.2.2.2
  refine ⟨eff.1.trans inv.global,?_,?_,?_,?_,?_,?_,frame.2.2.trans inv.barrier,eff.2.2.1.trans inv.site⟩
  · rw [eff.2.1]; split <;> simp [inv.length]
  · intro i hi
    rw [eff.2.1]
    split
    · rw [List.getElem?_set_ne (by dsimp [nextIndex]; omega)]; exact inv.old i hi
    · exact inv.old i hi
  · intro u hu active
    rw [eff.2.1]
    by_cases eq : u=t
    · subst u
      simp only [active,ite_true]
      have inside : nextIndex s k t < state.shared.length := lt_of_lt_of_le (round_indices s b k hk t).2.1 extent
      rw [List.getElem?_set_self inside]
      have reads := round_reads s k hk global start state ready inv.old t active
      simp [nodeValue,reads.1,reads.2,ready.global]
    · have ne : nextIndex s k t ≠ nextIndex s k u := by
        intro h; apply eq; apply Fin.ext; dsimp [nextIndex] at h; omega
      split
      · rw [List.getElem?_set_ne ne]
        apply inv.written u (by have : u.val ≠ count := fun h => eq (Fin.ext h); omega) active
      · apply inv.written u (by have : u.val ≠ count := fun h => eq (Fin.ext h); omega) active
  · intro u
    by_cases eq : u=t
    · subst u; simpa [t] using pc15
    · rw [others u eq,inv.pc]
      have ne : u.val ≠ count := fun h => eq (Fin.ext h)
      have same : u.val<count+1 ↔ u.val<count := by omega
      simp only [same]
  · intro u
    by_cases eq : u=t
    · subst u; exact frame.2.1.trans (inv.live t)
    · rw [others u eq]; exact inv.live u
  · intro u
    by_cases eq : u=t
    · subst u; exact ⟨eff.2.2.2.1.trans (inv.regs t).1,
        eff.2.2.2.2.1.trans (inv.regs t).2.1,eff.2.2.2.2.2.1.trans (inv.regs t).2.2⟩
    · rw [others u eq]; exact inv.regs u

/-- Every lane executes its actual reduction segment, then the group completes
its next barrier. The earlier plane is preserved throughout the sweep. -/
theorem round_phase_exists (s : Shape) (b : Bounds s) (k : Nat) (hk : k<s.depth)
    (global : List Word) (start : Parallel.State s.threads) (ready : PlaneReady s global start k) :
    ∃ events final, Runs (config s b) (program s) start events final ∧
      PlaneReady s global final (k+1) ∧ final.shared.length = start.shared.length := by
  have sweep : ∀ count, count≤s.threads → ∃ events state,
      Runs (config s b) (program s) start events state ∧ RoundInvariant s start state k count := by
    intro count bound
    induction count with
    | zero =>
      refine ⟨[],start,Runs.nil,rfl,rfl,?_,?_,?_,ready.live,?_,rfl,rfl⟩
      · intro i _; rfl
      · intro t ht; omega
      · intro t; simp [ready.pc]
      · intro t; exact ⟨rfl,rfl,rfl⟩
    | succ count ih =>
      obtain ⟨events,state,run,inv⟩ := ih (by omega)
      let t : Fin s.threads := ⟨count,by omega⟩
      have extent : s.sharedWords ≤ state.shared.length := by rw [inv.length]; exact ready.extent
      obtain ⟨next,step⟩ := round_run s b k hk state t
        ((inv.regs t).1.trans (ready.regs t).1) ((inv.regs t).2.1.trans (ready.regs t).2.1)
        extent (by simp [inv.pc,t]) (inv.live t) (by simp [inv.barrier,ready.barrier,Barrier.reset])
      exact ⟨events++next,_,runs_append run step,round_invariant_step s b k hk global start state ready count (by omega) inv⟩
  obtain ⟨events,state,run,inv⟩ := sweep s.threads (Nat.le_refl _)
  have pcs : ∀ t, (state.lanes t).scalar.pc = 22+16*k+15 := by intro t; simp [inv.pc,t.isLt]
  have fetch : (program s)[22+16*k+15]? = some (.sync 0) := by
    rw [round_fetch s k hk 15 (by simp)]; exact round_barrier s k
  obtain ⟨arrivals,release⟩ := barrier_round_exists (config s b) state (program s) (22+16*k+15) (k+1)
    pcs inv.live (inv.barrier.trans ready.barrier) (inv.site.trans ready.site) fetch
    (by change 94=94 ∧ 70≤70; decide)
  refine ⟨events++arrivals,afterRound state (k+1),runs_append run release,?_,inv.length⟩
  refine ⟨inv.global.trans ready.global,?_,?_,inv.live,?_,rfl,rfl,?_⟩
  · change s.sharedWords ≤ state.shared.length; rw [inv.length]; exact ready.extent
  · intro t; simp [afterRound,pcs]; omega
  · intro t; exact ⟨(inv.regs t).1.trans (ready.regs t).1,
      (inv.regs t).2.1.trans (ready.regs t).2.1,(inv.regs t).2.2.trans (ready.regs t).2.2⟩
  · intro r c hr hc
    have width : 2^(s.depth-(k+1)) ≤ s.width := Nat.pow_le_pow_right (by decide) (Nat.sub_le _ _)
    let t : Fin s.threads := ⟨s.thread r c,thread_bound s r c hr (lt_of_lt_of_le hc width)⟩
    have coords := thread_coordinates s r c (lt_of_lt_of_le hc width)
    have result := inv.written t t.isLt (by simpa [t,coords] using hc)
    simpa [afterRound,nextIndex,t,coords,Shape.scratch,ready.global,Nat.add_comm] using result

/-- Products initialize the first shared plane and the coordinates required by
all later rounds. No caller initialization of working registers is assumed. -/
theorem first_plane_exists (s : Shape) (b : Bounds s) (global shared : List Word)
    (seeds : Fin s.threads → Scalar.State)
    (globalBound : s.globalWords ≤ global.length) (sharedBound : s.sharedWords ≤ shared.length) :
    ∃ events state, Runs (config s b) (program s) (initial s global shared seeds) events state ∧
      PlaneReady s global state 0 ∧ state.shared.length = shared.length := by
  obtain ⟨events,state,run,gs,ss,values,pcs,barrier,site,_,regs⟩ :=
    product_phase_exists s b global shared seeds globalBound sharedBound
  refine ⟨events,state,run,⟨gs,?_,?_,?_,regs,barrier,site,?_⟩,ss⟩
  · rw [ss]; exact sharedBound
  · intro t; simpa using (pcs t).1
  · intro t; exact (pcs t).2
  · intro r c hr hc
    have width : c<s.width := by simpa [Shape.width] using hc
    let t : Fin s.threads := ⟨s.thread r c,thread_bound s r c hr width⟩
    have coords := thread_coordinates s r c width
    simpa [Shape.scratch,t,coords] using values t

/-- A selected fetched execution reaches the final reduction plane, with each
row's tree root calculated from the original global input array. -/
theorem reduction_exists (s : Shape) (b : Bounds s) (global shared : List Word)
    (seeds : Fin s.threads → Scalar.State)
    (globalBound : s.globalWords ≤ global.length) (sharedBound : s.sharedWords ≤ shared.length) :
    ∃ events state, Runs (config s b) (program s) (initial s global shared seeds) events state ∧
      PlaneReady s global state s.depth ∧ state.shared.length = shared.length := by
  have each : ∀ k, k≤s.depth → ∃ events state,
      Runs (config s b) (program s) (initial s global shared seeds) events state ∧
      PlaneReady s global state k ∧ state.shared.length = shared.length := by
    intro k bound
    induction k with
    | zero => exact first_plane_exists s b global shared seeds globalBound sharedBound
    | succ k ih =>
      obtain ⟨events,state,run,ready,length⟩ := ih (by omega)
      obtain ⟨next,final,step,done,extent⟩ := round_phase_exists s b k (by omega) global state ready
      exact ⟨events++next,final,runs_append run step,done,extent.trans length⟩
  exact each s.depth (Nat.le_refl _)

end Ptx.Scalar.Parallel.Dense

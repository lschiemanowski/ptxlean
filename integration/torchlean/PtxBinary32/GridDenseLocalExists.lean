import PtxBinary32.GridDenseLocalControl

/-! One bounded group has a complete fetched execution from arbitrary input
words and register seeds. All phases use actual instruction and barrier steps. -/
namespace Ptx.Scalar.Parallel.GridDense.Local
open Dense

theorem product_exists (s : Shape) (b : GridDense.Bounds s) (g : Fin s.rows)
    (global shared : List Word) (seeds : Fin s.threads → Scalar.State)
    (globalBound : s.globalWords≤global.length) (sharedBound : Dense.Compact.sharedWords s≤shared.length) :
    ∃ events final, Parallel.ConcreteRuns ((GridDense.config s b).group g) (Dense.Compact.program s)
      (initial s g global shared seeds) events final ∧
      (∀ t, (final.lanes t).scalar.pc=22 ∧ (final.lanes t).halted=false) ∧
      final.barrier=Barrier.reset 1 ∧ final.site=none := by
  let cfg := (GridDense.config s b).group g
  have eligible : Mixed.Eligible cfg.target := by change 94=94 ∧ 70≤70; decide
  have ordinary : NoSync ((Dense.Compact.products s).take 21) := by intro r; simp [Dense.Compact.products,pointer,scalar,guarded]
  obtain ⟨events,state,run,pcs,reset,site⟩ := segment_sweep (cfg := cfg) ordinary 0 0
    (start := initial s g global shared seeds) (fun _ => rfl) (fun _ => rfl) rfl rfl (Dense.Compact.products_fetch s) eligible (by
      intro events state run t pc
      have lengths := runs_memory_length run.toRuns
      have tid := initial_reg s b g global shared seeds run t pc
      obtain ⟨events,segment⟩ := Dense.Compact.product_segment s b.arithmetic cfg state t (thread s g t) tid
        (by simp only [initial] at lengths; omega)
        (by simp only [initial] at lengths; omega)
      exact ⟨events,_,segment⟩)
  have positions : ∀ t, (state.lanes t).scalar.pc=21 := fun t => by simpa using (pcs t).1
  have fetch : (Dense.Compact.program s)[21]?=some (.sync 0) := by simp [Dense.Compact.program,Dense.Compact.products,pointer]
  obtain ⟨arrivals,release⟩ := barrier_round_concrete cfg state (Dense.Compact.program s) 21 0 positions
    (fun t => (pcs t).2) reset site fetch eligible
  exact ⟨events++arrivals,afterRound state 0,concrete_runs_append run release,
    fun t => ⟨by simp [afterRound,positions],(pcs t).2⟩,rfl,rfl⟩

theorem reduction_exists (s : Shape) (b : GridDense.Bounds s) (g : Fin s.rows)
    (global shared : List Word) (seeds : Fin s.threads → Scalar.State)
    (globalBound : s.globalWords≤global.length) (sharedBound : Dense.Compact.sharedWords s≤shared.length) :
    ∃ events final, Parallel.ConcreteRuns ((GridDense.config s b).group g) (Dense.Compact.program s)
      (initial s g global shared seeds) events final ∧
      (∀ t, (final.lanes t).scalar.pc=22+16*s.depth ∧ (final.lanes t).halted=false) ∧
      final.barrier=Barrier.reset (s.depth+1) ∧ final.site=none := by
  let cfg := (GridDense.config s b).group g
  have eligible : Mixed.Eligible cfg.target := by change 94=94 ∧ 70≤70; decide
  have each : ∀ k, k≤s.depth → ∃ events state,
      Parallel.ConcreteRuns cfg (Dense.Compact.program s) (initial s g global shared seeds) events state ∧
      (∀ t, (state.lanes t).scalar.pc=22+16*k ∧ (state.lanes t).halted=false) ∧
      state.barrier=Barrier.reset (k+1) ∧ state.site=none := by
    intro k bound
    induction k with
    | zero => simpa using product_exists s b g global shared seeds globalBound sharedBound
    | succ k ih =>
      obtain ⟨events,state,run,pcs,reset,site⟩ := ih (by omega)
      have ordinary : NoSync ((Dense.Compact.round s k).take 15) := by intro r; simp [Dense.Compact.round,pointer,scalar,guarded]
      have fetch : Fetches (Dense.Compact.program s) (22+16*k) ((Dense.Compact.round s k).take 15) := by
        intro i hi
        have bound : i<15 := by simpa using hi
        rw [Dense.Compact.round_fetch s k (by omega) i (by simp; omega)]
        simp [bound]
      obtain ⟨next,middle,tail,positions,reset,site⟩ := segment_sweep (cfg := cfg) ordinary (22+16*k) (k+1)
        (fun t => (pcs t).1) (fun t => (pcs t).2) reset site fetch eligible (by
          intro next middle tail t pc
          have combined := concrete_runs_append run tail
          have lengths := runs_memory_length combined.toRuns
          have coords := entry_regs s b g global shared seeds combined t k (by omega) pc
          have regular := Dense.Compact.round_regular s b.arithmetic k (by omega) cfg middle t (thread s g t)
            coords.1 coords.2.1 (by simp only [initial] at lengths; omega)
          exact ⟨_,_,segmentReference_concrete regular⟩)
      have atBarrier : ∀ t, (middle.lanes t).scalar.pc=22+16*k+15 := fun t => by simpa using (positions t).1
      have fetch : (Dense.Compact.program s)[22+16*k+15]?=some (.sync 0) := by
        rw [Dense.Compact.round_fetch s k (by omega) 15 (by simp)]; exact Dense.Compact.round_barrier s k
      obtain ⟨arrivals,release⟩ := barrier_round_concrete cfg middle (Dense.Compact.program s) (22+16*k+15) (k+1)
        atBarrier (fun t => (positions t).2) reset site fetch eligible
      refine ⟨(events++next)++arrivals,afterRound middle (k+1),
        concrete_runs_append (concrete_runs_append run tail) release,?_,rfl,rfl⟩
      intro t
      exact ⟨by simp [afterRound,atBarrier]; omega,(positions t).2⟩
  exact each s.depth (by rfl)

/-- Completion is obtained without assuming any intermediate products or sums,
admitted memory observations, numerical ranges, or desired output values. -/
theorem completed_exists (s : Shape) (b : GridDense.Bounds s) (g : Fin s.rows)
    (global shared : List Word) (seeds : Fin s.threads → Scalar.State)
    (globalBound : s.globalWords≤global.length) (sharedBound : Dense.Compact.sharedWords s≤shared.length) :
    ∃ events final, Parallel.ConcreteRuns ((GridDense.config s b).group g) (Dense.Compact.program s)
      (initial s g global shared seeds) events final ∧ ∀ t, (final.lanes t).halted=true := by
  let cfg := (GridDense.config s b).group g
  have eligible : Mixed.Eligible cfg.target := by change 94=94 ∧ 70≤70; decide
  obtain ⟨events,state,run,pcs,reset,site⟩ := reduction_exists s b g global shared seeds globalBound sharedBound
  have ordinary : NoSync ((Dense.Compact.output s).take 19) := by intro r; simp [Dense.Compact.output,pointer,scalar,guarded]
  have fetch : Fetches (Dense.Compact.program s) (22+16*s.depth) ((Dense.Compact.output s).take 19) := by
    intro i hi
    have bound : i<19 := by simpa using hi
    rw [Dense.Compact.output_fetch s i (by simp; omega)]
    simp [bound]
  obtain ⟨next,middle,tail,positions,reset,site⟩ := segment_sweep (cfg := cfg) ordinary (22+16*s.depth) (s.depth+1)
    (fun t => (pcs t).1) (fun t => (pcs t).2) reset site fetch eligible (by
      intro next middle tail t pc
      have combined := concrete_runs_append run tail
      have lengths := runs_memory_length combined.toRuns
      have coords := entry_regs s b g global shared seeds combined t s.depth (by rfl) pc
      have regular := Dense.Compact.output_regular s b.arithmetic cfg middle t (thread s g t) coords
        (by simp only [initial] at lengths; omega)
        (by simp only [initial] at lengths; omega)
      exact ⟨_,_,segmentReference_concrete regular⟩)
  have atExit : ∀ t, (middle.lanes t).scalar.pc=22+16*s.depth+19 := fun t => by simpa using (positions t).1
  have fetch : (Dense.Compact.program s)[22+16*s.depth+19]?=some .exit := by
    rw [Dense.Compact.output_fetch s 19 (by simp)]; exact Dense.Compact.output_exit s
  obtain ⟨exits,final,exitRun,halted⟩ := exit_sweep (cfg := cfg) (22+16*s.depth+19) (s.depth+1)
    atExit (fun t => (positions t).2) reset fetch eligible
  exact ⟨(events++next)++exits,final,concrete_runs_append (concrete_runs_append run tail) exitRun,halted⟩
end Ptx.Scalar.Parallel.GridDense.Local

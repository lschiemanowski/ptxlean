import PtxBinary32.DenseOutput

/-! A complete selected instruction execution and its stored output words.
This is deliberately a candidate-execution result: memory-model admission and
universal correctness for all admitted candidates remain separate obligations. -/
namespace Ptx.Scalar.Parallel.Dense

structure OutputInvariant (s : Shape) (start state : Parallel.State s.threads) (count : Nat) : Prop where
  length : state.global.length = start.global.length
  shared : state.shared = start.shared
  inputs : ∀ i, i<s.outputBase → state.global[i]? = start.global[i]?
  outputs : ∀ r, r<s.rows → s.thread r 0<count →
    state.global[s.outputBase+r]? = some (forwardWord s start.global r)
  done : ∀ t : Fin s.threads, t.val<count →
    (state.lanes t).halted = true ∧ (state.lanes t).scalar.pc = 22+16*s.depth+19
  untouched : ∀ t : Fin s.threads, count≤t.val → state.lanes t = start.lanes t
  barrier : state.barrier = start.barrier
  site : state.site = start.site

theorem output_value (s : Shape) (global : List Word) (start state : Parallel.State s.threads)
    (ready : PlaneReady s global start s.depth)
    (shared : state.shared = start.shared)
    (inputs : ∀ i, i<s.outputBase → state.global[i]? = start.global[i]?)
    (t : Fin s.threads) (leader : t.val%s.width=0) :
    outputValue s state t = forwardWord s global (t.val/s.width) := by
  have row := (coordinates s t).1
  have id := (coordinates s t).2.2
  have root : rootIndex s t = s.scratch s.depth (t.val/s.width) 0 := by
    simp only [leader,Shape.thread,Nat.add_zero] at id
    dsimp [rootIndex,Shape.scratch,Shape.thread]; omega
  have value := ready.values (t.val/s.width) 0 row (by simp)
  unfold outputValue forwardWord affineWord
  rw [List.getElem!_eq_getElem?_getD,shared,root,value]
  rw [List.getElem!_eq_getElem?_getD,inputs _ (output_indices s t).2.1,ready.global]
  simp [biasIndex,Nat.add_comm]

theorem output_invariant_step (s : Shape) (b : Bounds s) (global : List Word)
    (start state : Parallel.State s.threads) (ready : PlaneReady s global start s.depth)
    (globalBound : s.globalWords ≤ global.length) (count : Nat) (bound : count<s.threads)
    (inv : OutputInvariant s start state count) :
    OutputInvariant s start (outputDone s b state ⟨count,bound⟩) (count+1) := by
  let t : Fin s.threads := ⟨count,bound⟩
  have lane : state.lanes t = start.lanes t := inv.untouched t (by rfl)
  have regs := ready.regs t
  rw [← lane] at regs
  have gs : s.globalWords ≤ state.global.length := by rw [inv.length,ready.global]; exact globalBound
  have ss : s.sharedWords ≤ state.shared.length := by rw [inv.shared]; exact ready.extent
  have eff := output_effect s b state t regs gs ss
  have frame := (segmentReference_sound (output_regular s b state t regs gs ss)).frame
  change ((outputFinish s b state t).lanes t).scalar.pc = (state.lanes t).scalar.pc + ((output s).take 19).length ∧
    ((outputFinish s b state t).lanes t).halted = (state.lanes t).halted ∧
    (outputFinish s b state t).barrier = state.barrier at frame
  have pcs : (state.lanes t).scalar.pc = 22+16*s.depth := by rw [lane]; exact ready.pc t
  have pc19 : ((outputDone s b state t).lanes t).scalar.pc = 22+16*s.depth+19 := by
    simpa [outputDone,setLane,pcs] using frame.1
  have others : ∀ u, u≠t → (outputDone s b state t).lanes u = state.lanes u := by
    intro u ne
    simp [outputDone,setLane,Function.update,ne,eff.2.2.2 u ne]
  have memory : (outputDone s b state t).global =
      (if t.val%s.width=0 then state.global.set (outputIndex s t) (outputValue s state t) else state.global) := eff.1
  refine ⟨?_,eff.2.1.trans inv.shared,?_,?_,?_,?_,frame.2.2.trans inv.barrier,eff.2.2.1.trans inv.site⟩
  · rw [memory]; split <;> simp [inv.length]
  · intro i hi
    rw [memory]
    split
    · rw [List.getElem?_set_ne (by have := (output_indices s t).2.2.1; omega)]; exact inv.inputs i hi
    · exact inv.inputs i hi
  · intro r hr processed
    rw [memory]
    by_cases same : s.thread r 0 = count
    · have coords := thread_coordinates s r 0 (width_positive s)
      have row : t.val/s.width=r := by simpa [t,same] using coords.1
      have leader : t.val%s.width=0 := by simpa [t,same] using coords.2
      have index : outputIndex s t = s.outputBase+r := by simp [outputIndex,row,Nat.add_comm]
      rw [ite_eq_left leader,← index,List.getElem?_set_self (lt_of_lt_of_le (output_indices s t).2.2.2 gs)]
      rw [output_value s global start state ready inv.shared inv.inputs t leader,row,ready.global]
    · have previous : s.thread r 0<count := by omega
      split
      · rename_i leader
        have ne : outputIndex s t ≠ s.outputBase+r := by
          intro eq
          have row : t.val/s.width=r := by dsimp [outputIndex] at eq; omega
          have id := (coordinates s t).2.2
          rw [row,leader] at id
          exact same (by simpa [t] using id)
        rw [List.getElem?_set_ne ne]; exact inv.outputs r hr previous
      · exact inv.outputs r hr previous
  · intro u hu
    by_cases eq : u=t
    · subst u; exact ⟨by simp [outputDone,setLane,t],pc19⟩
    · rw [others u eq]
      exact inv.done u (by have : u.val≠count := fun h => eq (Fin.ext h); omega)
  · intro u hu
    have ne : u≠t := by intro eq; subst u; dsimp [t] at hu; omega
    rw [others u ne]; exact inv.untouched u (by omega)

/-- All output segments and exits are fetched; input words and shared storage
are preserved. The result is for the selected software arithmetic choices. -/
theorem output_phase_exists (s : Shape) (b : Bounds s) (global : List Word)
    (start : Parallel.State s.threads) (ready : PlaneReady s global start s.depth)
    (globalBound : s.globalWords ≤ global.length) :
    ∃ events final, Runs (config s b) (program s) start events final ∧
      OutputInvariant s start final s.threads := by
  have sweep : ∀ count, count≤s.threads → ∃ events state,
      Runs (config s b) (program s) start events state ∧ OutputInvariant s start state count := by
    intro count bound
    induction count with
    | zero =>
      refine ⟨[],start,Runs.nil,rfl,rfl,?_,?_,?_,?_,rfl,rfl⟩
      · intro i _; rfl
      · intro r _ h; omega
      · intro t h; omega
      · intro t _; rfl
    | succ count ih =>
      obtain ⟨events,state,run,inv⟩ := ih (by omega)
      let t : Fin s.threads := ⟨count,by omega⟩
      have lane : state.lanes t = start.lanes t := inv.untouched t (Nat.le_refl _)
      have regs := ready.regs t
      rw [← lane] at regs
      have gs : s.globalWords ≤ state.global.length := by rw [inv.length,ready.global]; exact globalBound
      have ss : s.sharedWords ≤ state.shared.length := by rw [inv.shared]; exact ready.extent
      obtain ⟨next,step⟩ := output_run s b state t regs gs ss (by rw [lane]; exact ready.pc t)
        (by rw [lane]; exact ready.live t) (by simp [inv.barrier,ready.barrier,Barrier.reset])
      exact ⟨events++next,_,runs_append run step,
        output_invariant_step s b global start state ready globalBound count (by omega) inv⟩
  exact sweep s.threads (Nat.le_refl _)

/-- Complete candidate execution of the parallel forward kernel. The theorem
contains no assumed intermediate loads or output values. It does not assert
admission under the PTX memory graph or correctness of every candidate run. -/
theorem selected_forward_exists (s : Shape) (b : Bounds s) (global shared : List Word)
    (seeds : Fin s.threads → Scalar.State)
    (globalBound : s.globalWords ≤ global.length) (sharedBound : s.sharedWords ≤ shared.length) :
    ∃ events final, Runs (config s b) (program s) (initial s global shared seeds) events final ∧
      (∀ t, (final.lanes t).halted = true ∧ (final.lanes t).scalar.pc = (program s).length-1) ∧
      (∀ r, r<s.rows → final.global[s.outputBase+r]? = some (forwardWord s global r)) ∧
      (∀ i, i<s.outputBase → final.global[i]? = global[i]?) ∧
      final.global.length = global.length ∧ final.shared.length = shared.length ∧
      final.barrier = Barrier.reset (s.depth+1) ∧ final.site = none ∧
      (∀ event ∈ events, AccessSafe (initial s global shared seeds) event) := by
  obtain ⟨first,state,run,ready,length⟩ := reduction_exists s b global shared seeds globalBound sharedBound
  obtain ⟨last,final,finish,inv⟩ := output_phase_exists s b global state ready globalBound
  refine ⟨first++last,final,runs_append run finish,?_,?_,?_,?_,?_,inv.barrier.trans ready.barrier,
    inv.site.trans ready.site,?_⟩
  · intro t
    have done := inv.done t t.isLt
    exact ⟨done.1,by rw [done.2,program_length]; omega⟩
  · intro r hr
    simpa [ready.global] using inv.outputs r hr (thread_bound s r 0 hr (width_positive s))
  · intro i hi; simpa [ready.global] using inv.inputs i hi
  · rw [inv.length,ready.global]
  · rw [inv.shared]; exact length
  · intro event member; exact runs_access_safe (runs_append run finish) event member

/-- Numerical accuracy for the words actually stored by a complete selected
execution. RowInput supplies finite operand interpretations, encoding errors and
checked intermediate ranges; matching its tree and bias to the original input
array is required. This does not identify that ideal tree with TorchLean's graph
or prove the execution's admission under the PTX memory constraints. -/
theorem selected_forward_accuracy (s : Shape) (b : Bounds s) (global shared : List Word)
    (seeds : Fin s.threads → Scalar.State)
    (globalBound : s.globalWords ≤ global.length) (sharedBound : s.sharedWords ≤ shared.length) :
    ∃ events final, Runs (config s b) (program s) (initial s global shared seeds) events final ∧
      (∀ t, (final.lanes t).halted = true) ∧
      (∀ r, r<s.rows → ∀ i : Ptx.Binary32.Reduction.RowInput,
        Ptx.Binary32.Reduction.words i.tree =
          Ptx.Binary32.Reduction.balanced s.depth 0 (operands s global r) →
        i.bias = global[s.biasBase+r]! →
        Ptx.Binary32.finiteReal final.global[s.outputBase+r]! = some (max i.affine 0) ∧
          |max i.affine 0-max i.idealAffine 0| ≤ i.error) := by
  obtain ⟨events,final,run,done,values,_⟩ := selected_forward_exists s b global shared seeds globalBound sharedBound
  refine ⟨events,final,run,fun t => (done t).1,?_⟩
  intro r hr i tree bias
  rw [List.getElem!_eq_getElem?_getD,values r hr]
  exact forward_accuracy s global r i tree bias

end Ptx.Scalar.Parallel.Dense

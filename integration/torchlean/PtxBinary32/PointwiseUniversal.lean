import PtxBinary32.PointwiseMachine

namespace Ptx.Scalar.Parallel.Pointwise

theorem run_data (op : Op) (l : Layout n) (global shared : List Word) (seeds : Fin n → Scalar.State)
    {cfg : Config n} {events : List (Event n)} {final : State n}
    (run : Runs cfg (program op) (initial l global shared seeds) events final)
    (source co) (valid : Admitted op l global shared seeds run source co) : Stores op l global events := by
  have reads : Reads op l global events := by
    intro t space occ effect member memory load
    obtain ⟨q,hq,atQ⟩ := List.mem_iff_getElem.mp member
    obtain ⟨right,pc,value⟩ := read_source op l global shared seeds run source co valid q t space occ effect (by simpa [hq] using atQ) memory load
    cases right <;> simp_all
  have aux {state : State n} {events : List (Event n)} {final : State n}
      (run : Runs cfg (program op) state events final) (aligned : Aligned state)
      (inv : DataInvariant op l global state) (reads : Reads op l global events) :
      Stores op l global events := by
    induction run with
    | nil => intro _ _ _ _ member; simp at member
    | cons step tail ih =>
      obtain ⟨nextInv,stored⟩ := step_data op l global step inv aligned
        (fun t sp occ e member => reads t sp occ e (List.mem_append_left _ member))
      have rest := ih (step_aligned step aligned) nextInv
        (fun t sp occ e member => reads t sp occ e (List.mem_append_right _ member))
      intro t sp occ e member
      rcases List.mem_append.mp member with h | h
      · exact stored t sp occ e h
      · exact rest t sp occ e h
  apply aux run (initial_aligned l global shared seeds) _ reads
  intro t
  constructor <;> simp [initial,seed]

theorem completed_pc (op : Op) (l : Layout n) (global shared : List Word) (seeds : Fin n → Scalar.State)
    {cfg : Config n} {events : List (Event n)} {final : State n}
    (run : Runs cfg (program op) (initial l global shared seeds) events final)
    (t : Fin n) (halted : (final.lanes t).halted=true) : storePC op<(final.lanes t).scalar.pc := by
  obtain ⟨pc,fetch,member⟩ := Control.halted_exit_origin run (straight op) t rfl halted
  have length := (List.getElem?_eq_some_iff.mp fetch).choose
  have site : pc=storePC op+1 := by
    cases op <;> simp [program,body] at length
    all_goals interval_cases pc <;> simp_all [program,body,storePC,localOp,clear]
  obtain ⟨p,hp,atP⟩ := List.mem_iff_getElem.mp member
  have bound := ((Control.runs_progress run (straight op)).emitted p (.exit t pc) t pc
    (by simpa [hp] using atP) rfl).2
  have upper := (Control.cursor_bounds final t).2
  omega

theorem completed_store (op : Op) (l : Layout n) (global shared : List Word) (seeds : Fin n → Scalar.State)
    {cfg : Config n} {events : List (Event n)} {final : State n}
    (run : Runs cfg (program op) (initial l global shared seeds) events final)
    (t : Fin n) (halted : (final.lanes t).halted=true) :
    ∃ occ effect, .scalar t (some .global) occ ∈ events ∧ occ.memory=some effect ∧ effect.kind=.store := by
  have fetch : (program op)[storePC op]?=some (.memory .global (.plain (.store (.reg 2) (.reg 6)))) := by cases op <;> rfl
  obtain ⟨before,after,middle,out,u,candidate,trace,frontRun,step,_,old,new⟩ :=
    Control.crossing_step run (straight op) t (storePC op) (Nat.zero_le _) (completed_pc op l global shared seeds run t halted)
  obtain ⟨owner,next,occ,ev,emitted⟩ := Control.memory_crossing step (straight op)
    (runs_aligned frontRun (initial_aligned l global shared seeds)) (by rw [old]; exact fetch) (by omega)
  subst u
  simp only [Scalar.eval,Scalar.Instr.plain,Scalar.Guard.eval,↓reduceIte] at ev
  split at ev
  · contradiction
  · obtain ⟨_,rfl⟩ := Scalar.StepResult.next.inj ev
    refine ⟨Scalar.occurrence {(middle.lanes t).scalar with memory := middle.global}
      (.plain (.store (.reg 2) (.reg 6))) true
      (some ⟨.store,(middle.lanes t).scalar.addrs 2,(middle.lanes t).scalar.regs 6⟩),
      ⟨.store,(middle.lanes t).scalar.addrs 2,(middle.lanes t).scalar.regs 6⟩,?_,rfl,rfl⟩
    simp [trace,emitted,arena,Scalar.Instr.plain,Scalar.Operand32.eval,Scalar.Operand64.eval]

theorem written_result (op : Op) (l : Layout n) (global shared : List Word) (seeds : Fin n → Scalar.State)
    {cfg : Config n} {events : List (Event n)} {final : State n}
    (run : Runs cfg (program op) (initial l global shared seeds) events final)
    (known : Stores op l global events) (event : Event n) (member : event ∈ events) (index : Nat) (value : Word)
    (written : Replay.writtenAt .global index event=some value) :
    ∃ t : Fin n, index=l.output t ∧ Result op global[l.left t]! global[l.right t]! value := by
  obtain ⟨t,occ,address,rfl,memory,atIndex⟩ := Replay.writtenAt_some .global index event value written
  obtain ⟨_,_,addr⟩ := store_address op l global shared seeds run t .global occ ⟨.store,address,value⟩ member memory rfl
  change address=Dense.bytePointer (l.output t) at addr
  have bound : l.output t<l.prefixWords+n := by have := t.isLt; unfold Layout.output; omega
  refine ⟨t,?_,known t .global occ ⟨.store,address,value⟩ member memory rfl⟩
  simpa [addr,pointer_index l _ bound] using atIndex.symm

/-- Every admitted completed interleaving stores its actual permitted pointwise
results. No desired load values, lane schedule or intermediate results are premises. -/
theorem completed (op : Op) (l : Layout n) (global shared : List Word) (seeds : Fin n → Scalar.State)
    {cfg : Config n} {events : List (Event n)} {final : State n}
    (run : Runs cfg (program op) (initial l global shared seeds) events final)
    (halted : ∀ t, (final.lanes t).halted=true) (source co) (valid : Admitted op l global shared seeds run source co) :
    (∀ t, ∃ value, final.global[l.output t]?=some value ∧ Result op global[l.left t]! global[l.right t]! value) ∧
    (∀ i, i<l.prefixWords → final.global[i]?=global[i]?) ∧
    final.global.length=global.length ∧ final.shared.length=shared.length ∧
    (∀ event ∈ events, AccessSafe (initial l global shared seeds) event) := by
  have known := run_data op l global shared seeds run source co valid
  refine ⟨?_,?_,(runs_memory_length run).1,(runs_memory_length run).2,runs_access_safe run⟩
  · intro t
    have summary := Replay.run_value run .global (l.output t)
    dsimp [Replay.arena,Replay.arrays,initial] at summary
    cases last : Replay.latestWrite .global (l.output t) events with
    | none =>
      obtain ⟨occ,effect,member,memory,store⟩ := completed_store op l global shared seeds run t (halted t)
      obtain ⟨_,_,addr⟩ := store_address op l global shared seeds run t .global occ effect member memory store
      have absent := (Replay.latestWrite_none .global (l.output t) events).mp last _ member
      have bound : l.output t<l.prefixWords+n := by have := t.isLt; unfold Layout.output; omega
      simp [Replay.writtenAt,memory,store,addr,pointer_index l _ bound] at absent
    | some value =>
      obtain ⟨before,event,after,split,written,_⟩ := Replay.latestWrite_origin .global _ events value last
      obtain ⟨u,idx,correct⟩ := written_result op l global shared seeds run known event (by simp [split]) _ value written
      have eq : t=u := by apply Fin.ext; unfold Layout.output at idx; omega
      exact ⟨value,by simpa [last] using summary,by simpa [eq] using correct⟩
  · intro i hi
    have summary := Replay.run_value run .global i
    dsimp [Replay.arena,Replay.arrays,initial] at summary
    cases last : Replay.latestWrite .global i events with
    | none => simpa [last] using summary
    | some value =>
      obtain ⟨before,event,after,split,written,_⟩ := Replay.latestWrite_origin .global _ events value last
      obtain ⟨u,idx,_⟩ := written_result op l global shared seeds run known event (by simp [split]) _ value written
      unfold Layout.output at idx; omega

end Ptx.Scalar.Parallel.Pointwise

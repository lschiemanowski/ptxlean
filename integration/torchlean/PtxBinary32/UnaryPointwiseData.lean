import PtxBinary32.UnaryPointwiseReads

/-! Register meanings along every fetched lane, retaining actual permitted
intermediate arithmetic choices. Initial-memory read meanings are supplied only
by the separate memory-admission proof. -/
namespace Ptx.Scalar.UnaryPointwise
open ParallelUnary

def Scratch : Op → Nat → Word → Word → Word → Prop
  | .shifted,0,_,_,_ | .shifted,1,_,_,_ | .shifted,2,_,_,_ => True
  | .shifted,3,_,b,out => Binary32.Results .mul b 0xbf800000 out
  | .shifted,4,a,b,out => ∃negative, Binary32.Results .mul b 0xbf800000 negative ∧
      Binary32.Results .add a negative out
  | .shifted,5,a,b,out => ∃negative shifted, Binary32.Results .mul b 0xbf800000 negative ∧
      Binary32.Results .add a negative shifted ∧ Binary32.Results .mul shifted Binary32.ExpArgument.constantWord out
  | .shifted,_,a,b,out => Result .shifted a b out
  | .normalize,0,_,_,_ | .normalize,1,_,_,_ | .normalize,2,_,_,_ => True
  | .normalize,3,_,b,out => Binary32.Reciprocal.Results b out
  | .normalize,_,a,b,out => Result .normalize a b out

def Data (op : Op) (a b : Word) (s : Scalar.State) : Prop :=
  s.pc≤exitPC op ∧ (1≤s.pc → s.regs 0=a) ∧ (2≤s.pc → s.regs 1=b) ∧ Scratch op s.pc a b (s.regs 2)

theorem initial_data (op : Op) (common : Nat) (before : List Word) (seeds : Fin n→Scalar.State) (t : Fin n) :
    Data op before[t.val]! before[common]! ((initial common before seeds).lanes t).scalar := by
  cases op <;> simp [Data,initial,Scratch,exitPC,storePC]

private theorem binary_data (op : Op) (a b : Word) (s next : Scalar.State)
    (data : Data op a b s) (fetch : (program op)[s.pc]?=some (.binary i))
    (eval : Scalar.Binary32.Eval i s next event) : Data op a b next := by
  rcases data with ⟨bound,left,right,scratch⟩
  generalize hpc : s.pc=pc at *
  cases op <;> simp only [exitPC,storePC] at bound
  all_goals interval_cases pc
  all_goals simp [program,body,arithmetic,ownLoad,commonLoad,ownStore,exitInstr] at fetch
  all_goals subst i
  all_goals
    cases eval
    all_goals simp_all [Scalar.Guard.eval,Data,Scratch,exitPC,storePC,ShiftedExp.negate,ShiftedExp.shift,ShiftedExp.convert,
      Normalize.multiply,Scalar.Operand32.eval,Scalar.update,Result,SoftmaxMemory.NormalizeStages]
    all_goals first
      | exact ⟨_,scratch,by assumption⟩
      | (obtain ⟨negative,hn,hs⟩ := scratch; exact ⟨negative,hn,_,hs,by assumption⟩)

private theorem exponential_data (op : Op) (a b : Word) (s next : Scalar.State)
    (data : Data op a b s) (fetch : (program op)[s.pc]?=some (.exponential i))
    (eval : Scalar.Exponential.Eval i s next event) : Data op a b next := by
  rcases data with ⟨bound,left,right,scratch⟩
  generalize hpc : s.pc=pc at *
  cases op <;> simp only [exitPC,storePC] at bound
  all_goals interval_cases pc
  all_goals simp [program,body,arithmetic,ownLoad,commonLoad,ownStore,exitInstr] at fetch
  all_goals subst i
  all_goals
    cases eval
    all_goals simp_all [Scalar.Guard.eval,Data,Scratch,exitPC,storePC,ShiftedExp.exponential,Scalar.Operand32.eval,Scalar.update,
      Result,SoftmaxMemory.ShiftedStages]
    all_goals
      obtain ⟨negative,hn,shifted,hs,hp⟩ := scratch
      exact ⟨negative,hn,shifted,hs,_,hp,by assumption⟩

private theorem reciprocal_data (op : Op) (a b : Word) (s next : Scalar.State)
    (data : Data op a b s) (fetch : (program op)[s.pc]?=some (.reciprocal i))
    (eval : Scalar.Reciprocal.Eval i s next event) : Data op a b next := by
  rcases data with ⟨bound,left,right,scratch⟩
  generalize hpc : s.pc=pc at *
  cases op <;> simp only [exitPC,storePC] at bound
  all_goals interval_cases pc
  all_goals simp [program,body,arithmetic,ownLoad,commonLoad,ownStore,exitInstr] at fetch
  all_goals subst i
  all_goals
    cases eval
    all_goals simp_all [Scalar.Guard.eval,Data,Scratch,exitPC,storePC,Normalize.reciprocal,Scalar.Operand32.eval,Scalar.update]

/-- Meanings of the actual emitted load values, discharged by memory admission. -/
def ReadValues (before : List Word) (common : Nat) (event : Event n) : Prop :=
  ∀effect, event.memory=some effect → effect.kind=.load →
    effect.value=if event.pc=0 then before[event.thread.val]! else before[common]!

private theorem scalar_data (op : Op) (a b : Word) (s next : Scalar.State)
    (data : Data op a b s) (fetch : (program op)[s.pc]?=some (.scalar i))
    (eval : Scalar.eval candidate i s=.next next event)
    (read : ∀effect, event.memory=some effect → effect.kind=.load → effect.value=if event.pc=0 then a else b) :
    Data op a b next := by
  rcases scalar_sites op s.pc i fetch with ⟨pc,rfl⟩|⟨pc,rfl⟩|⟨pc,rfl⟩|⟨pc,rfl⟩
  all_goals simp only [Scalar.eval,Scalar.Instr.plain,Scalar.Guard.eval,Scalar.Operand64.eval,↓reduceIte] at eval
  all_goals first | contradiction | skip
  all_goals split at eval <;> first | contradiction | skip
  all_goals obtain ⟨rfl,rfl⟩ := Scalar.StepResult.next.inj eval
  all_goals try have value := read _ rfl rfl
  all_goals cases op <;> simp_all [Data,Scratch,Scalar.occurrence,Scalar.update,exitPC,storePC]

/-- One fetched transition preserves each thread's exact arithmetic meanings. -/
theorem step_data {s next : ParallelUnary.State n}
    (data : ∀t,Data op before[t.val]! before[common]! (s.lanes t).scalar)
    (step : ParallelUnary.Step target (program op) candidate selected s next event)
    (reads : ReadValues before common event) :
    ∀t,Data op before[t.val]! before[common]! (next.lanes t).scalar := by
  obtain ⟨_,_,i,fetch,exec⟩ := step
  have selectedData : Data op before[selected.val]! before[common]! (next.lanes selected).scalar := by
    cases exec with
    | scalarNext eval =>
      have old : Data op before[selected.val]! before[common]! (input s selected) := data selected
      have h := scalar_data op _ _ _ _ old fetch eval reads
      simpa [install] using h
    | scalarHalted eval =>
      have same := (Scalar.eval_halted eval).1
      simpa [install,same,input,Data] using data selected
    | binary eval => simpa [setLane] using binary_data op _ _ _ _ (data selected) fetch eval
    | exponential eval => simpa [setLane] using exponential_data op _ _ _ _ (data selected) fetch eval
    | reciprocal eval => simpa [setLane] using reciprocal_data op _ _ _ _ (data selected) fetch eval
  intro t
  by_cases eq : t=selected
  · subst t; exact selectedData
  · rw [ParallelUnary.exec_other exec t eq]; exact data t

/-- All prefixes preserve register meaning once their emitted reads have been
identified with original memory by the graph proof. -/
theorem runs_data {s final : ParallelUnary.State n}
    (data : ∀t,Data op before[t.val]! before[common]! (s.lanes t).scalar)
    (run : ParallelUnary.Runs target (program op) s events final)
    (reads : ∀event∈events, ReadValues before common event) :
    ∀t,Data op before[t.val]! before[common]! (final.lanes t).scalar := by
  induction run with
  | nil => exact data
  | cons step rest ih =>
    exact ih (step_data data step (reads _ (by simp))) (fun event member => reads event (by simp [member]))

variable {n common : Nat} {op : Op} {before : List Word}
variable {seeds : Fin n→Scalar.State} {events : List (Event n)} {final : ParallelUnary.State n}

theorem admitted_reads
    (run : ParallelUnary.Runs target (program op) (initial common before seeds) events final)
    (bounds : Bounds n common before) (source co)
    (valid : Memory.Admitted (program op) before events source co) :
    ∀event∈events, ReadValues before common event := by
  intro event member effect memory read
  have fit : common<2^62 := bounds.2.2.2.1.trans bounds.2.2.2.2
  have value := reads_initial run bounds.2.2.1 fit source co valid event effect member memory read
  rcases run_memory run member memory with h|h|h
  · rw [h.2.2,pointer_index _ (event.thread.isLt.trans_le (bounds.2.2.1.trans fit.le))] at value
    simpa [h.1] using value
  · rw [h.2.2,pointer_index _ fit] at value
    simpa [h.1] using value
  · simp [read] at h

/-- Graph admission discharges all candidate-read premises of the register proof. -/
theorem run_data
    (run : ParallelUnary.Runs target (program op) (initial common before seeds) events final)
    (bounds : Bounds n common before) (source co)
    (valid : Memory.Admitted (program op) before events source co) :
    ∀t,Data op before[t.val]! before[common]! (final.lanes t).scalar :=
  runs_data (initial_data op common before seeds) run (admitted_reads run bounds source co valid)

private theorem step_store_result {s next : ParallelUnary.State n}
    (data : ∀t,Data op before[t.val]! before[common]! (s.lanes t).scalar)
    (step : ParallelUnary.Step target (program op) candidate selected s next event)
    (memory : event.memory=some effect) (store : effect.kind=.store) :
    Result op before[event.thread.val]! before[common]! effect.value := by
  obtain ⟨_,_,i,fetch,exec⟩ := step
  cases exec with
  | scalarNext eval =>
    rcases scalar_sites op _ _ fetch with ⟨pc,rfl⟩|⟨pc,rfl⟩|⟨pc,rfl⟩|⟨pc,rfl⟩
    all_goals simp only [Scalar.eval,Scalar.Instr.plain,Scalar.Guard.eval,Scalar.Operand64.eval,↓reduceIte] at eval
    all_goals first | contradiction | skip
    all_goals split at eval <;> first | contradiction | skip
    all_goals
      obtain ⟨rfl,rfl⟩ := Scalar.StepResult.next.inj eval
      simp only [Event.memory,Scalar.occurrence,Option.some.injEq] at memory
      subst effect
    all_goals first | contradiction | skip
    all_goals
      have h := (data selected).2.2.2
      cases op <;> simpa [Scratch,storePC,pc,Event.thread,Scalar.Operand32.eval,input] using h
  | scalarHalted eval => simp [Event.memory,(Scalar.eval_halted eval).2] at memory
  | binary _ | exponential _ | reciprocal _ => simp [Event.memory] at memory

private theorem runs_store_results {s : ParallelUnary.State n}
    (data : ∀t,Data op before[t.val]! before[common]! (s.lanes t).scalar)
    (run : ParallelUnary.Runs target (program op) s events final)
    (reads : ∀event∈events, ReadValues before common event)
    (member : event∈events) (memory : event.memory=some effect) (store : effect.kind=.store) :
    Result op before[event.thread.val]! before[common]! effect.value := by
  induction run with
  | nil => simp at member
  | cons step rest ih =>
    cases member with
    | head => exact step_store_result data step memory store
    | tail _ member =>
      exact ih (step_data data step (reads _ (by simp)))
        (fun event member => reads event (by simp [member])) member

/-- Every actual stored value satisfies the intended unary arithmetic relation. -/
theorem store_results
    (run : ParallelUnary.Runs target (program op) (initial common before seeds) events final)
    (bounds : Bounds n common before) (source co)
    (valid : Memory.Admitted (program op) before events source co)
    (member : event∈events) (memory : event.memory=some effect) (store : effect.kind=.store) :
    Result op before[event.thread.val]! before[common]! effect.value :=
  runs_store_results (initial_data op common before seeds) run (admitted_reads run bounds source co valid)
    member memory store

end Ptx.Scalar.UnaryPointwise

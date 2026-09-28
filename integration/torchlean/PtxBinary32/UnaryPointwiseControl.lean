import PtxBinary32.UnaryPointwiseProgram
import PtxBinary32.ParallelUnary

/-! Launch-installed pointer ownership for all candidate interleavings. The
proofs concern the actual fetched instruction and emitted memory occurrence. -/
namespace Ptx.Scalar.UnaryPointwise
open ParallelUnary

def pointer (index : Nat) : Address := SoftmaxMemory.address index

def initial (common : Nat) (memory : List Word) (seeds : Fin n → Scalar.State) : ParallelUnary.State n :=
  ⟨fun t => ⟨{seeds t with
    pc:=0
    addrs:=Scalar.update (Scalar.update (seeds t).addrs 0 (pointer t.val)) 1 (pointer common)},false⟩,memory⟩

def Addresses (common : Nat) (s : ParallelUnary.State n) : Prop :=
  ∀t, (s.lanes t).scalar.addrs 0=pointer t.val ∧ (s.lanes t).scalar.addrs 1=pointer common

theorem initial_addresses (common : Nat) (memory : List Word) (seeds : Fin n → Scalar.State) :
    Addresses common (initial common memory seeds) := by simp [Addresses,initial,Scalar.update]

private theorem scalar_addresses {s next : Scalar.State} {i : Scalar.Instr}
    (allowed : ScalarAllowed i) (eval : Scalar.eval candidate i s=.next next event) : next.addrs=s.addrs := by
  rcases allowed with rfl | rfl | rfl | rfl
  all_goals simp only [Scalar.eval,Scalar.Instr.plain,Scalar.Guard.eval,Scalar.Operand64.eval,↓reduceIte] at eval
  all_goals first | contradiction | skip
  all_goals split at eval <;> first | contradiction | skip
  all_goals obtain ⟨rfl,rfl⟩ := Scalar.StepResult.next.inj eval; rfl

theorem step_addresses {s next : ParallelUnary.State n}
    (addresses : Addresses common s)
    (step : ParallelUnary.Step target (program op) candidate selected s next event) : Addresses common next := by
  obtain ⟨_,_,i,fetch,exec⟩ := step
  have addrFrame : (next.lanes selected).scalar.addrs=(s.lanes selected).scalar.addrs := by
    cases exec with
    | scalarNext eval =>
      have allowed := scalar_allowed op _ _ fetch
      simpa [install,input] using scalar_addresses allowed eval
    | scalarHalted eval =>
      have same := (Scalar.eval_halted eval).1
      simp [install,same,input]
    | binary eval => simpa [setLane] using (Scalar.Binary32.eval_frame _ _ _ _ eval).2.2.1
    | exponential eval => simpa [setLane] using (Scalar.Exponential.eval_frame _ _ _ _ eval).2.2.1
    | reciprocal eval => simpa [setLane] using (Scalar.Reciprocal.eval_frame _ _ _ _ eval).2.2.1
  intro t
  by_cases eq : t=selected
  · subst t; rw [addrFrame]; exact addresses _
  · have other := ParallelUnary.exec_other exec t eq
    rw [other]; exact addresses _

theorem runs_addresses {s final : ParallelUnary.State n}
    (addresses : Addresses common s)
    (run : ParallelUnary.Runs target (program op) s events final) : Addresses common final := by
  induction run with
  | nil => exact addresses
  | cons step _ ih => exact ih (step_addresses addresses step)

/-- Loads use either the issuer's own input or the common read-only scalar;
every store writes the issuer's own output cell. -/
theorem step_memory {s next : ParallelUnary.State n}
    (addresses : Addresses common s)
    (step : ParallelUnary.Step target (program op) candidate selected s next event)
    (memory : event.memory=some effect) :
    event.thread=selected ∧
      ((event.pc=0 ∧ effect.kind=.load ∧ effect.address=pointer selected.val) ∨
       (event.pc=1 ∧ effect.kind=.load ∧ effect.address=pointer common) ∨
       (event.pc=storePC op ∧ effect.kind=.store ∧ effect.address=pointer selected.val)) := by
  obtain ⟨_,_,i,fetch,exec⟩ := step
  cases exec with
  | scalarNext eval =>
    have sites := scalar_sites op _ _ fetch
    rcases sites with ⟨pc,rfl⟩|⟨pc,rfl⟩|⟨pc,rfl⟩|⟨pc,rfl⟩
    all_goals simp only [Scalar.eval,Scalar.Instr.plain,Scalar.Guard.eval,Scalar.Operand64.eval,↓reduceIte] at eval
    all_goals first | contradiction | skip
    all_goals split at eval <;> first | contradiction | skip
    all_goals
      obtain ⟨rfl,rfl⟩ := Scalar.StepResult.next.inj eval
      simp only [Event.memory,Scalar.occurrence,Option.some.injEq] at memory
      subst effect
      simp [Event.thread,Event.pc,Scalar.occurrence,input,pc,(addresses selected).1,(addresses selected).2]
  | scalarHalted eval => simp [Event.memory,(Scalar.eval_halted eval).2] at memory
  | binary _ | exponential _ | reciprocal _ => simp [Event.memory] at memory

/-- Ownership is derived for every occurrence of an arbitrary candidate run. -/
theorem runs_memory {n common : Nat} {op : Op}
    {events : List (Event n)} {event : Event n} {effect : MemoryEffect}
    {s final : ParallelUnary.State n} (addresses : Addresses common s)
    (run : ParallelUnary.Runs target (program op) s events final)
    (member : event∈events) (memory : event.memory=some effect) :
      ((event.pc=0 ∧ effect.kind=.load ∧ effect.address=pointer event.thread.val) ∨
       (event.pc=1 ∧ effect.kind=.load ∧ effect.address=pointer common) ∨
       (event.pc=storePC op ∧ effect.kind=.store ∧ effect.address=pointer event.thread.val)) := by
  induction run with
  | nil => simp at member
  | cons step _ ih =>
    cases member with
    | head =>
      obtain ⟨thread,sites⟩ := step_memory addresses step memory
      simpa [thread] using sites
    | tail _ member => exact ih (step_addresses addresses step) member

theorem run_memory {n common : Nat} {op : Op} {before : List Word}
    {seeds : Fin n → Scalar.State} {events : List (Event n)} {event : Event n}
    {effect : MemoryEffect} {final : ParallelUnary.State n}
    (run : ParallelUnary.Runs target (program op) (initial common before seeds) events final)
    (member : event∈events) (memory : event.memory=some effect) :
      ((event.pc=0 ∧ effect.kind=.load ∧ effect.address=pointer event.thread.val) ∨
       (event.pc=1 ∧ effect.kind=.load ∧ effect.address=pointer common) ∨
       (event.pc=storePC op ∧ effect.kind=.store ∧ effect.address=pointer event.thread.val)) :=
  runs_memory (initial_addresses _ _ _) run member memory

def HaltSite (op : Op) (s : ParallelUnary.State n) : Prop :=
  ∀t, (s.lanes t).halted=true → (s.lanes t).scalar.pc=exitPC op

theorem step_halt_site {s next : ParallelUnary.State n} (sites : HaltSite op s)
    (step : ParallelUnary.Step target (program op) candidate selected s next event) : HaltSite op next := by
  obtain ⟨_,live,i,fetch,exec⟩ := step
  have selectedSite : (next.lanes selected).halted=true → (next.lanes selected).scalar.pc=exitPC op := by
    cases exec with
    | scalarNext eval => simp [install,live]
    | scalarHalted eval =>
      have same := (Scalar.eval_halted eval).1
      have pc : (s.lanes selected).scalar.pc=exitPC op := by
        rcases scalar_sites op _ _ fetch with ⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨h,_⟩
        all_goals first | exact h | skip
        all_goals simp only [Scalar.eval,Scalar.Instr.plain,Scalar.Guard.eval,Scalar.Operand64.eval,↓reduceIte] at eval
        all_goals split at eval <;> contradiction
      simpa [install,same,input] using pc
    | binary _ | exponential _ | reciprocal _ => simp [setLane,live]
  intro t halted
  by_cases eq : t=selected
  · subst t; exact selectedSite halted
  · have other := ParallelUnary.exec_other exec t eq
    rw [other] at halted ⊢
    exact sites t halted

theorem runs_halt_site {s final : ParallelUnary.State n} (sites : HaltSite op s)
    (run : ParallelUnary.Runs target (program op) s events final) : HaltSite op final := by
  induction run with
  | nil => exact sites
  | cons step rest ih => exact ih (step_halt_site sites step)

theorem completed_pc {n common : Nat} {op : Op} {before : List Word}
    {seeds : Fin n → Scalar.State} {events : List (Event n)} {final : ParallelUnary.State n} (run : ParallelUnary.Runs target (program op) (initial common before seeds) events final)
    (t : Fin n) (halted : (final.lanes t).halted=true) : (final.lanes t).scalar.pc=exitPC op := by
  exact runs_halt_site (by simp [HaltSite,initial]) run t halted

end Ptx.Scalar.UnaryPointwise

import PoissonPTX.ConcurrentBarrier

/-! Executable witnesses for the relational candidate machine. Chosen load
words are parameters; successful execution alone does not validate their sources. -/
namespace PtxTorchLean.Poisson.PTX.Concurrent

/-- The interpreter uses a caller-chosen word for loads and the existing
canonical floating-point interpreter for arithmetic. -/
def evaluate (op : Op) (s : PTX.State) (word : Word) : Option (PTX.State × Option Access) :=
  match op with
  | .load64 sp dst addr =>
    if Valid64 (s.start sp) (s.bytes sp) (addr.eval s).toNat then
      some (assign s dst word,some ⟨sp,⟨s.pc,false,(addr.eval s).toNat,word⟩⟩)
    else none
  | .store64 sp addr src =>
    if Valid64 (s.start sp) (s.bytes sp) (addr.eval s).toNat then
      some (put s sp (addr.eval s).toNat (src.eval s),some ⟨sp,⟨s.pc,true,(addr.eval s).toNat,src.eval s⟩⟩)
    else none
  | op => (PTX.eval op s).map fun next => (next,none)

theorem evaluate_sound (h : evaluate op s word=some (next,access)) : Data op s next access := by
  cases op with
  | load64 sp dst addr =>
    simp only [evaluate] at h
    split at h
    · cases Option.some.inj h; exact Data.load ‹_›
    · simp at h
  | store64 sp addr src =>
    simp only [evaluate] at h
    split at h
    · cases Option.some.inj h; exact Data.store ‹_›
    · simp at h
  | _ =>
    simp only [evaluate,Option.map_eq_some_iff] at h
    obtain ⟨t,ht,he⟩ := h
    cases he
    exact Data.ordinary rfl (eval_sound ht)

def tick (cfg : Config n) (program : List Instr) (choose : Fin n → Nat → Word)
    (thread : Fin n) (s : State n) : Option (Outcome n) := do
  if s.barrier.arrived thread then none else do
    match ← program[(s.lanes thread).pc]? with
    | .data op =>
      let (next,access) ← evaluate op (s.lanes thread) (choose thread (s.lanes thread).pc)
      some ⟨setLane s thread next,access.toList.map (Event.data thread)⟩
    | .skip active target => some ⟨setLane s thread
        {s.lanes thread with pc := if thread.val<active then (s.lanes thread).pc+1 else target},[]⟩
    | .sync resource => some (synchronize cfg s thread resource)

theorem tick_sound (h : tick cfg program choose thread s=some out) : Step cfg program thread s out := by
  unfold tick at h
  split at h
  · simp at h
  · have fresh : s.barrier.arrived thread=false := by simpa using ‹¬s.barrier.arrived thread=true›
    cases fetch : program[(s.lanes thread).pc]? with
    | none => simp [fetch] at h
    | some i =>
      refine ⟨fresh,i,fetch,?_⟩
      cases i with
      | data op =>
        cases ev : evaluate op (s.lanes thread) (choose thread (s.lanes thread).pc) with
        | none => simp [fetch,ev] at h
        | some pair =>
          rcases pair with ⟨next,access⟩
          simp [fetch,ev] at h
          subst out
          exact Dispatch.data (evaluate_sound ev)
      | skip active target => simp [fetch] at h; subst out; exact Dispatch.skip
      | sync resource => simp [fetch] at h; subst out; exact Dispatch.sync

def execute (cfg : Config n) (program : List Instr) (choose : Fin n → Nat → Word) :
    List (Fin n) → State n → Option (Outcome n)
  | [],s => some ⟨s,[]⟩
  | t::rest,s => do
    let first ← tick cfg program choose t s
    let last ← execute cfg program choose rest first.state
    return ⟨last.state,first.events++last.events⟩

theorem execute_sound (h : execute cfg program choose schedule s=some out) :
    Runs cfg program s out.events out.state := by
  induction schedule generalizing s out with
  | nil => simp only [execute,Option.some.injEq] at h; subst out; exact Runs.nil
  | cons thread rest ih =>
    cases hf : tick cfg program choose thread s with
    | none => simp [execute,hf] at h
    | some first =>
      cases hl : execute cfg program choose rest first.state with
      | none => simp [execute,hf,hl] at h
      | some last =>
        simp [execute,hf,hl] at h
        subst out
        exact Runs.cons (tick_sound hf) (ih hl)

end PtxTorchLean.Poisson.PTX.Concurrent

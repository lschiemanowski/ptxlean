import PtxBinary32.PointwiseData

namespace Ptx.Scalar.Parallel.Pointwise

/-- Local values in every thread, independently of the scheduler. -/
def DataInvariant (op : Op) (l : Layout n) (global : List Word) (state : Parallel.State n) : Prop :=
  ∀ t, Data op global[l.left t]! global[l.right t]! (state.lanes t).scalar

/-- Only actual emitted stores are included in the induction history. -/
def Stores (op : Op) (l : Layout n) (global : List Word) (events : List (Event n)) : Prop :=
  ∀ t space occ effect, .scalar t (some space) occ ∈ events → occ.memory=some effect → effect.kind=.store →
    Result op global[l.left t]! global[l.right t]! effect.value

def Reads (op : Op) (l : Layout n) (global : List Word) (events : List (Event n)) : Prop :=
  ∀ t space occ effect, .scalar t (some space) occ ∈ events → occ.memory=some effect → effect.kind=.load →
    ((occ.pc=0 → effect.value=global[l.left t]!) ∧ (occ.pc=1 → effect.value=global[l.right t]!))

private theorem data_memory (data : Data op a b state) (memory : List Word) : Data op a b {state with memory := memory} := by
  rcases data with ⟨l,r,v,z,s⟩
  exact ⟨l,r,v,z,s⟩

private theorem install {l : Layout n} {state : State n} (inv : DataInvariant op l global state) (t : Fin n) (lane : Lane)
    (data : Data op global[l.left t]! global[l.right t]! lane.scalar) : DataInvariant op l global (setLane state t lane) := by
  intro u
  by_cases eq : u=t
  · subst u; simpa [setLane] using data
  · simpa [setLane,Function.update,eq] using inv u

private theorem local_no_memory (op : Op) (pc : Nat) (i : Scalar.Instr)
    (fetch : (program op)[pc]?=some (.localStep i)) : Memory.Prior.memoryKind i.op=none := by
  have bound : pc<(program op).length := (List.getElem?_eq_some_iff.mp fetch).choose
  cases op <;> simp [program,body] at bound
  all_goals interval_cases pc <;> simp [program,body,localOp,clear] at fetch
  all_goals subst i; rfl

private theorem no_scalar_halt (op : Op) (l : Layout n) (i : Scalar.Instr) {pc : Nat} {wrapped : Instr} (fetch : (program op)[pc]?=some wrapped)
    (form : wrapped=.localStep i ∨ ∃ space, wrapped=.memory space i) : Scalar.eval candidate i a≠.halted next occ := by
  have straight := straight op _ (List.mem_of_getElem? fetch)
  have op : Control.StraightOp i.op := by rcases form with rfl | ⟨_,rfl⟩ <;> exact straight
  rcases i with ⟨guard,inst⟩
  cases inst <;> simp only [Control.StraightOp] at op
  all_goals cases enabled : guard.eval a <;> simp only [Scalar.eval,enabled,↓reduceIte]
  all_goals first | contradiction | (solve | simp) | (split <;> simp)

private theorem scalar_machine (op : Op) (l : Layout n) (global : List Word)
    (state : Parallel.State n) (t : Fin n) (space : Option Space) (i : Scalar.Instr)
    (inv : DataInvariant op l global state)
    (fetch : (program op)[(state.lanes t).scalar.pc]?=some (match space with | none => .localStep i | some sp => .memory sp i))
    (reads : Reads op l global (scalarStep candidate t space i state).events) :
    DataInvariant op l global (scalarStep candidate t space i state).state ∧ Stores op l global (scalarStep candidate t space i state).events := by
  let a := {(state.lanes t).scalar with memory := arena state space}
  have old : Data op global[l.left t]! global[l.right t]! a := data_memory (inv t) _
  have fetched : (program op)[a.pc]?=some (.localStep i) ∨ ∃ sp, (program op)[a.pc]?=some (.memory sp i) := by
    cases space with
    | none => exact .inl fetch
    | some sp => exact .inr ⟨sp,fetch⟩
  cases ev : Scalar.eval candidate i a with
  | next next occ =>
    dsimp only [a] at ev
    have readValues : ∀ effect, occ.memory=some effect → effect.kind=.load → ((occ.pc=0 → effect.value=global[l.left t]!) ∧ (occ.pc=1 → effect.value=global[l.right t]!)) := by
      intro effect memory load
      cases space with
      | none =>
        have kind := (Memory.Prior.eval_effect_origin candidate i a next occ effect ev memory).2.2.2
        change Memory.Prior.memoryKind i.op=some effect.kind at kind
        rw [local_no_memory op _ i fetch] at kind
        contradiction
      | some sp =>
        apply reads t sp occ effect _ memory load
        cases sp <;> simp [scalarStep,ev]
    have data := scalar_data op global[l.left t]! global[l.right t]! a next i occ old fetched ev readValues
    have installed := install inv t {state.lanes t with scalar := next} data
    constructor
    · cases space with
      | none => simpa only [scalarStep,ev] using installed
      | some sp => cases sp <;> simpa only [scalarStep,ev,DataInvariant,setLane] using installed
    · intro owner seen other effect member memory store
      have eq : owner=t ∧ some seen=space ∧ other=occ := by
        cases space with
        | none => simpa [scalarStep,ev] using member
        | some sp => cases sp <;> simpa [scalarStep,ev] using member
      obtain ⟨rfl,rfl,rfl⟩ := eq
      exact scalar_store_data op global[l.left owner]! global[l.right owner]! a next i seen _ effect old fetch ev memory store
  | halted next occ =>
    dsimp only [a] at ev
    exact False.elim (no_scalar_halt op l i fetch (by cases space <;> simp) ev)
  | fault reason =>
    dsimp only [a] at ev
    constructor
    · simpa [scalarStep,ev] using inv
    · intro owner seen other effect member; simp [scalarStep,ev] at member
  | unsupported spelling =>
    dsimp only [a] at ev
    constructor
    · simpa [scalarStep,ev] using inv
    · intro owner seen other effect member; simp [scalarStep,ev] at member

theorem dispatch_data (op : Op) (l : Layout n) (global : List Word)
    {cfg : Config n} {state : Parallel.State n} {candidate : Option Word} {t : Fin n} {i : Instr} {out : Outcome n} (step : Dispatch cfg candidate t i state out)
    (fetch : (program op)[(state.lanes t).scalar.pc]?=some i)
    (inv : DataInvariant op l global state) (aligned : Aligned state) (reads : Reads op l global out.events) :
    DataInvariant op l global out.state ∧ Stores op l global out.events := by
  cases step with
  | localStep => exact scalar_machine op l global state t none _ inv fetch reads
  | memory => exact scalar_machine op l global state t (some _) _ inv fetch reads
  | binary32 ev =>
    refine ⟨install inv t _ (fp_data op global[l.left t]! global[l.right t]! _ _ _ _ (inv t) fetch ev),?_⟩
    intro owner space occ effect member; simp at member
  | exit =>
    refine ⟨install inv t _ (inv t),?_⟩
    intro owner space occ effect member; simp at member
  | sync =>
    have member := List.mem_of_getElem? fetch
    cases op <;> simp [program,body,localOp,clear] at member

theorem step_data (op : Op) (l : Layout n) (global : List Word)
    {cfg : Config n} {state : Parallel.State n} {candidate : Option Word} {t : Fin n} {out : Outcome n} (step : Step cfg (program op) candidate t state out)
    (inv : DataInvariant op l global state) (aligned : Aligned state) (reads : Reads op l global out.events) :
    DataInvariant op l global out.state ∧ Stores op l global out.events := by
  have h := step.2
  split at h
  · subst out; exact ⟨inv,by intro _ _ _ _ member; simp at member⟩
  · split at h
    · subst out; exact ⟨inv,by intro _ _ _ _ member; simp at member⟩
    · split at h
      · subst out; exact ⟨inv,by intro _ _ _ _ member; simp at member⟩
      · exact dispatch_data op l global h (by assumption) inv aligned reads

/-- Scalar events occupy the sole event position of their machine step. -/
theorem scalar_step_singleton {state : Parallel.State n}
    (step : Step cfg code candidate t state out) (member : .scalar owner space occ ∈ out.events) :
    out.events=[.scalar owner space occ] := by
  have h := step.2
  split at h
  · subst out; simp at member
  · split at h
    · subst out; simp at member
    · split at h
      · subst out; simp at member
      · cases h with
        | localStep =>
          rename_i i fetch
          cases ev : Scalar.eval candidate i {(state.lanes t).scalar with memory := arena state none} <;>
            simp [scalarStep,ev] at member ⊢
          all_goals obtain ⟨rfl,rfl,rfl⟩ := member; simp
        | memory =>
          rename_i seen i fetch
          cases ev : Scalar.eval candidate i {(state.lanes t).scalar with memory := arena state (some seen)} <;>
            cases seen <;> simp [scalarStep,ev] at member ⊢
          all_goals obtain ⟨rfl,rfl,rfl⟩ := member; simp
        | binary32 _ | exit => simp at member
        | sync =>
          rename_i resource fetch
          cases hd : (Barrier.step (barrierConfig cfg state t) state.barrier (barrierRequest cfg state t resource)).disposition <;>
            simp [synchronize,hd] at member

end Ptx.Scalar.Parallel.Pointwise

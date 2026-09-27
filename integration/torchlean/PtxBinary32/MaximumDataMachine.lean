import PtxBinary32.MaximumDataRules
import PtxBinary32.MaximumStoreData

namespace Ptx.Scalar.Parallel.Maximum

/-- Local values in every thread, independently of the scheduler. -/
def DataInvariant (d : Nat) (global : List Word) (state : Parallel.State (width d)) : Prop :=
  ∀ t, Data d global t (state.lanes t).scalar

/-- Only actual emitted stores are included in the induction history. -/
def Stores (d : Nat) (global : List Word) (events : List (Event (width d))) : Prop :=
  ∀ t space occ effect, .scalar t (some space) occ ∈ events → occ.memory=some effect → effect.kind=.store →
    StoreData d global t occ.pc effect.value

def Reads (d : Nat) (global : List Word) (events : List (Event (width d))) : Prop :=
  ∀ t space occ effect, .scalar t (some space) occ ∈ events → occ.memory=some effect → effect.kind=.load →
    ReadData d global t occ.pc effect.value

private theorem data_memory (data : Data d global t a) (memory : List Word) : Data d global t {a with memory := memory} := by
  rcases data with ⟨a,b,c,d,e,f,g,h,i,j,k,l,m,n,o,p⟩
  exact ⟨a,b,c,d,e,f,g,h,i,j,k,l,m,n,o,p⟩

private theorem install (inv : DataInvariant d global state) (t : Fin (width d)) (lane : Lane)
    (data : Data d global t lane.scalar) : DataInvariant d global (setLane state t lane) := by
  intro u
  by_cases eq : u=t
  · subst u; simpa [setLane] using data
  · simpa [setLane,Function.update,eq] using inv u

private theorem local_no_memory (d : Nat) (pc : Nat) (i : Scalar.Instr)
    (fetch : (program d)[pc]?=some (.localStep i)) : Memory.Prior.memoryKind i.op=none := by
  rcases program_segment d pc _ fetch with ⟨bound,h⟩ | ⟨k,hk,j,hj,site,h⟩ | ⟨j,hj,site,h⟩
  · interval_cases pc <;> simp [publish,publishCode,Dense.pointer,Dense.scalar,Dense.guarded] at h
    all_goals subst i; rfl
  · interval_cases j <;> simp [round,roundCode,roundPrefix,roundSuffix,Scalar.MaximumSelect.code,Dense.pointer,Dense.scalar,Dense.guarded] at h
    all_goals subst i; rfl
  · interval_cases j <;> simp [output,outputCode,Dense.pointer,Dense.scalar,Dense.guarded] at h
    all_goals subst i; rfl

private theorem no_scalar_halt (d : Nat) (i : Scalar.Instr) {pc : Nat} {wrapped : Instr} (fetch : (program d)[pc]?=some wrapped)
    (form : wrapped=.localStep i ∨ ∃ space, wrapped=.memory space i) : Scalar.eval candidate i a≠.halted next occ := by
  have straight := program_straight d _ (List.mem_of_getElem? fetch)
  have op : Control.StraightOp i.op := by rcases form with rfl | ⟨_,rfl⟩ <;> exact straight
  rcases i with ⟨guard,inst⟩
  cases inst <;> simp only [Control.StraightOp] at op
  all_goals cases enabled : guard.eval a <;> simp only [Scalar.eval,enabled,↓reduceIte]
  all_goals first | contradiction | (solve | simp) | (split <;> simp)

private theorem scalar_machine (d : Nat) (b : Bounds d) (global : List Word)
    (state : Parallel.State (width d)) (t : Fin (width d)) (space : Option Space) (i : Scalar.Instr)
    (inv : DataInvariant d global state)
    (fetch : (program d)[(state.lanes t).scalar.pc]?=some (match space with | none => .localStep i | some sp => .memory sp i))
    (reads : Reads d global (scalarStep candidate t space i state).events) :
    DataInvariant d global (scalarStep candidate t space i state).state ∧ Stores d global (scalarStep candidate t space i state).events := by
  let a := {(state.lanes t).scalar with memory := arena state space}
  have old : Data d global t a := data_memory (inv t) _
  have fetched : (program d)[a.pc]?=some (.localStep i) ∨ ∃ sp, (program d)[a.pc]?=some (.memory sp i) := by
    cases space with
    | none => exact .inl fetch
    | some sp => exact .inr ⟨sp,fetch⟩
  cases ev : Scalar.eval candidate i a with
  | next next occ =>
    dsimp only [a] at ev
    have readValues : ∀ effect, occ.memory=some effect → effect.kind=.load → ReadData d global t occ.pc effect.value := by
      intro effect memory load
      cases space with
      | none =>
        have kind := (Memory.Prior.eval_effect_origin candidate i a next occ effect ev memory).2.2.2
        change Memory.Prior.memoryKind i.op=some effect.kind at kind
        rw [local_no_memory d _ i fetch] at kind
        contradiction
      | some sp =>
        apply reads t sp occ effect _ memory load
        cases sp <;> simp [scalarStep,ev]
    have data := scalar_data d b global t a next i occ old fetched ev readValues
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
      exact scalar_store_data d global owner a next i seen _ effect old fetch ev memory store
  | halted next occ =>
    dsimp only [a] at ev
    exact False.elim (no_scalar_halt d i fetch (by cases space <;> simp) ev)
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

theorem dispatch_data (d : Nat) (b : Bounds d) (global : List Word)
    {state : Parallel.State (width d)} {candidate : Option Word} {t : Fin (width d)} {i : Instr} {out : Outcome (width d)} (step : Dispatch (config d) candidate t i state out)
    (fetch : (program d)[(state.lanes t).scalar.pc]?=some i)
    (inv : DataInvariant d global state) (aligned : Aligned state) (reads : Reads d global out.events) :
    DataInvariant d global out.state ∧ Stores d global out.events := by
  cases step with
  | localStep => exact scalar_machine d b global state t none _ inv fetch reads
  | memory => exact scalar_machine d b global state t (some _) _ inv fetch reads
  | binary32 ev => exact False.elim (no_fp d _ _ fetch)
  | exit =>
    refine ⟨install inv t _ (inv t),?_⟩
    intro owner space occ effect member; simp at member
  | sync =>
    rename_i resource
    cases hd : (Barrier.step (barrierConfig (config d) state t) state.barrier (barrierRequest (config d) state t resource)).disposition with
    | rejectedWrongKey =>
      refine ⟨by simpa [synchronize,hd] using inv,?_⟩
      intro owner space occ effect member; simp [synchronize,hd] at member
    | waiting =>
      refine ⟨by simpa [synchronize,hd,DataInvariant] using inv,?_⟩
      intro owner space occ effect member; simp [synchronize,hd] at member
    | released =>
      have pcs := release_aligned (config d) state t resource aligned hd
      constructor
      · intro u
        simpa [synchronize,hd] using barrier_data d global u (state.lanes u).scalar resource (inv u) (by rw [pcs]; exact fetch)
      · intro owner space occ effect member; simp [synchronize,hd] at member

theorem step_data (d : Nat) (b : Bounds d) (global : List Word)
    {state : Parallel.State (width d)} {candidate : Option Word} {t : Fin (width d)} {out : Outcome (width d)} (step : Step (config d) (program d) candidate t state out)
    (inv : DataInvariant d global state) (aligned : Aligned state) (reads : Reads d global out.events) :
    DataInvariant d global out.state ∧ Stores d global out.events := by
  have h := step.2
  split at h
  · subst out; exact ⟨inv,by intro _ _ _ _ member; simp at member⟩
  · split at h
    · subst out; exact ⟨inv,by intro _ _ _ _ member; simp at member⟩
    · split at h
      · subst out; exact ⟨inv,by intro _ _ _ _ member; simp at member⟩
      · exact dispatch_data d b global h (by assumption) inv aligned reads

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

end Ptx.Scalar.Parallel.Maximum

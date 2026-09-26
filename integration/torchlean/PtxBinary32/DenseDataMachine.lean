import PtxBinary32.DenseDataRules
import PtxBinary32.DenseStoreData

namespace Ptx.Scalar.Parallel.Dense

/-- Local values in every thread, independently of the scheduler. -/
def DataInvariant (s : Shape) (global : List Word) (state : Parallel.State s.threads) : Prop :=
  ∀ t, Data s global t (state.lanes t).scalar

/-- Only actual emitted stores are included in the induction history. -/
def Stores (s : Shape) (global : List Word) (events : List (Event s.threads)) : Prop :=
  ∀ t space occ effect, .scalar t (some space) occ ∈ events → occ.memory=some effect → effect.kind=.store →
    StoreData s global t occ.pc effect.value

def Reads (s : Shape) (global : List Word) (events : List (Event s.threads)) : Prop :=
  ∀ t space occ effect, .scalar t (some space) occ ∈ events → occ.memory=some effect → effect.kind=.load →
    ReadData s global t occ.pc effect.value

private theorem data_memory (data : Data s global t a) (memory : List Word) : Data s global t {a with memory := memory} := by
  rcases data with ⟨a,b,c,d,e,f,g,h,i,j,k,l,m,n,o,p⟩
  exact ⟨a,b,c,d,e,f,g,h,i,j,k,l,m,n,o,p⟩

private theorem install (inv : DataInvariant s global state) (t : Fin s.threads) (lane : Lane)
    (data : Data s global t lane.scalar) : DataInvariant s global (setLane state t lane) := by
  intro u
  by_cases eq : u=t
  · subst u; simpa [setLane] using data
  · simpa [setLane,Function.update,eq] using inv u

private theorem local_no_memory (s : Shape) (pc : Nat) (i : Scalar.Instr)
    (fetch : (program s)[pc]?=some (.localStep i)) : Memory.Prior.memoryKind i.op=none := by
  rcases program_segment s pc _ fetch with ⟨bound,h⟩ | ⟨k,hk,j,hj,site,h⟩ | ⟨j,hj,site,h⟩
  · interval_cases pc <;> simp [products,pointer,scalar,guarded] at h
    all_goals subst i; rfl
  · interval_cases j <;> simp [round,pointer,scalar,guarded] at h
    all_goals subst i; rfl
  · interval_cases j <;> simp [output,pointer,scalar,guarded] at h
    all_goals subst i; rfl

private theorem no_scalar_halt (s : Shape) (i : Scalar.Instr) {pc : Nat} {wrapped : Instr} (fetch : (program s)[pc]?=some wrapped)
    (form : wrapped=.localStep i ∨ ∃ space, wrapped=.memory space i) : Scalar.eval candidate i a≠.halted next occ := by
  have straight := program_straight s _ (List.mem_of_getElem? fetch)
  have op : Control.StraightOp i.op := by rcases form with rfl | ⟨_,rfl⟩ <;> exact straight
  rcases i with ⟨guard,inst⟩
  cases inst <;> simp only [Control.StraightOp] at op
  all_goals cases enabled : guard.eval a <;> simp only [Scalar.eval,enabled,↓reduceIte]
  all_goals first | contradiction | (solve | simp) | (split <;> simp)

private theorem scalar_machine (s : Shape) (b : Bounds s) (global : List Word)
    (state : Parallel.State s.threads) (t : Fin s.threads) (space : Option Space) (i : Scalar.Instr)
    (inv : DataInvariant s global state)
    (fetch : (program s)[(state.lanes t).scalar.pc]?=some (match space with | none => .localStep i | some sp => .memory sp i))
    (reads : Reads s global (scalarStep candidate t space i state).events) :
    DataInvariant s global (scalarStep candidate t space i state).state ∧ Stores s global (scalarStep candidate t space i state).events := by
  let a := {(state.lanes t).scalar with memory := arena state space}
  have old : Data s global t a := data_memory (inv t) _
  have fetched : (program s)[a.pc]?=some (.localStep i) ∨ ∃ sp, (program s)[a.pc]?=some (.memory sp i) := by
    cases space with
    | none => exact .inl fetch
    | some sp => exact .inr ⟨sp,fetch⟩
  cases ev : Scalar.eval candidate i a with
  | next next occ =>
    dsimp only [a] at ev
    have readValues : ∀ effect, occ.memory=some effect → effect.kind=.load → ReadData s global t occ.pc effect.value := by
      intro effect memory load
      cases space with
      | none =>
        have kind := (Memory.Prior.eval_effect_origin candidate i a next occ effect ev memory).2.2.2
        change Memory.Prior.memoryKind i.op=some effect.kind at kind
        rw [local_no_memory s _ i fetch] at kind
        contradiction
      | some sp =>
        apply reads t sp occ effect _ memory load
        cases sp <;> simp [scalarStep,ev]
    have data := scalar_data s b global t a next i occ old fetched ev readValues
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
      exact scalar_store_data s global owner a next i seen _ effect old fetch ev memory store
  | halted next occ =>
    dsimp only [a] at ev
    exact False.elim (no_scalar_halt s i fetch (by cases space <;> simp) ev)
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

theorem dispatch_data (s : Shape) (b : Bounds s) (global : List Word)
    {state : Parallel.State s.threads} {candidate : Option Word} {t : Fin s.threads} {i : Instr} {out : Outcome s.threads} (step : Dispatch (config s b) candidate t i state out)
    (fetch : (program s)[(state.lanes t).scalar.pc]?=some i)
    (inv : DataInvariant s global state) (aligned : Aligned state) (reads : Reads s global out.events) :
    DataInvariant s global out.state ∧ Stores s global out.events := by
  cases step with
  | localStep => exact scalar_machine s b global state t none _ inv fetch reads
  | memory => exact scalar_machine s b global state t (some _) _ inv fetch reads
  | binary32 ev =>
    refine ⟨install inv t _ (fp_data s global t _ _ _ _ (inv t) fetch ev),?_⟩
    intro owner space occ effect member; simp at member
  | exit =>
    refine ⟨install inv t _ (inv t),?_⟩
    intro owner space occ effect member; simp at member
  | sync =>
    rename_i resource
    cases hd : (Barrier.step (barrierConfig (config s b) state t) state.barrier (barrierRequest (config s b) state t resource)).disposition with
    | rejectedWrongKey =>
      refine ⟨by simpa [synchronize,hd] using inv,?_⟩
      intro owner space occ effect member; simp [synchronize,hd] at member
    | waiting =>
      refine ⟨by simpa [synchronize,hd,DataInvariant] using inv,?_⟩
      intro owner space occ effect member; simp [synchronize,hd] at member
    | released =>
      have pcs := release_aligned (config s b) state t resource aligned hd
      constructor
      · intro u
        simpa [synchronize,hd] using barrier_data s global u (state.lanes u).scalar resource (inv u) (by rw [pcs]; exact fetch)
      · intro owner space occ effect member; simp [synchronize,hd] at member

theorem step_data (s : Shape) (b : Bounds s) (global : List Word)
    {state : Parallel.State s.threads} {candidate : Option Word} {t : Fin s.threads} {out : Outcome s.threads} (step : Step (config s b) (program s) candidate t state out)
    (inv : DataInvariant s global state) (aligned : Aligned state) (reads : Reads s global out.events) :
    DataInvariant s global out.state ∧ Stores s global out.events := by
  have h := step.2
  split at h
  · subst out; exact ⟨inv,by intro _ _ _ _ member; simp at member⟩
  · split at h
    · subst out; exact ⟨inv,by intro _ _ _ _ member; simp at member⟩
    · split at h
      · subst out; exact ⟨inv,by intro _ _ _ _ member; simp at member⟩
      · exact dispatch_data s b global h (by assumption) inv aligned reads

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

end Ptx.Scalar.Parallel.Dense

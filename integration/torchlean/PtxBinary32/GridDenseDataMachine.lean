import PtxBinary32.GridDenseProgram
import PtxBinary32.CompactDenseDataRules
import PtxBinary32.DenseStoreData

/-! Per-group arithmetic invariants indexed by their global logical row/lane.
The local transition still reads the actual grid view supplied by the caller. -/
namespace Ptx.Scalar.Parallel.GridDense.LocalData
open Ptx.Scalar.Parallel.Dense
open GridDense (thread config Bounds)

/-- Local values in every thread, independently of the scheduler. -/
def DataInvariant (s : Dense.Shape) (global : List Word) (g : Fin s.rows) (state : Parallel.State s.width) : Prop :=
  ∀ t, Data s global (thread s g t) (state.lanes t).scalar

/-- Only actual emitted stores are included in the induction history. -/
def Stores (s : Dense.Shape) (global : List Word) (g : Fin s.rows) (events : List (Event s.width)) : Prop :=
  ∀ t space occ effect, .scalar t (some space) occ ∈ events → occ.memory=some effect → effect.kind=.store →
    StoreData s global (thread s g t) occ.pc effect.value

def Reads (s : Dense.Shape) (global : List Word) (g : Fin s.rows) (events : List (Event s.width)) : Prop :=
  ∀ t space occ effect, .scalar t (some space) occ ∈ events → occ.memory=some effect → effect.kind=.load →
    ReadData s global (thread s g t) occ.pc effect.value

private theorem data_memory (data : Data s global (thread s g t) a) (memory : List Word) : Data s global (thread s g t) {a with memory := memory} := by
  rcases data with ⟨a,b,c,d,e,f,g,h,i,j,k,l,m,n,o,p⟩
  exact ⟨a,b,c,d,e,f,g,h,i,j,k,l,m,n,o,p⟩

private theorem install (inv : DataInvariant s global g state) (t : Fin s.width) (lane : Lane)
    (data : Data s global (thread s g t) lane.scalar) : DataInvariant s global g (setLane state t lane) := by
  intro u
  by_cases eq : u=t
  · subst u; simpa [setLane] using data
  · simpa [setLane,Function.update,eq] using inv u

private theorem local_no_memory (s : Dense.Shape) (pc : Nat) (i : Scalar.Instr)
    (fetch : (Dense.Compact.program s)[pc]?=some (.localStep i)) : Memory.Prior.memoryKind i.op=none := by
  rcases Dense.Compact.program_segment s pc _ fetch with ⟨bound,h⟩ | ⟨k,hk,j,hj,site,h⟩ | ⟨j,hj,site,h⟩
  · interval_cases pc <;> simp [Dense.Compact.products,pointer,scalar,guarded] at h
    all_goals subst i; rfl
  · interval_cases j <;> simp [Dense.Compact.round,pointer,scalar,guarded] at h
    all_goals subst i; rfl
  · interval_cases j <;> simp [Dense.Compact.output,pointer,scalar,guarded] at h
    all_goals subst i; rfl

private theorem no_scalar_halt (s : Dense.Shape) (i : Scalar.Instr) {pc : Nat} {wrapped : Instr} (fetch : (Dense.Compact.program s)[pc]?=some wrapped)
    (form : wrapped=.localStep i ∨ ∃ space, wrapped=.memory space i) : Scalar.eval candidate i a≠.halted next occ := by
  have straight := Dense.Compact.program_straight s _ (List.mem_of_getElem? fetch)
  have op : Control.StraightOp i.op := by rcases form with rfl | ⟨_,rfl⟩ <;> exact straight
  rcases i with ⟨guard,inst⟩
  cases inst <;> simp only [Control.StraightOp] at op
  all_goals cases enabled : guard.eval a <;> simp only [Scalar.eval,enabled,↓reduceIte]
  all_goals first | contradiction | (solve | simp) | (split <;> simp)

private theorem scalar_machine (s : Dense.Shape) (b : Bounds s) (global : List Word) (g : Fin s.rows)
    (state : Parallel.State s.width) (t : Fin s.width) (space : Option Space) (i : Scalar.Instr)
    (inv : DataInvariant s global g state)
    (fetch : (Dense.Compact.program s)[(state.lanes t).scalar.pc]?=some (match space with | none => .localStep i | some sp => .memory sp i))
    (reads : Reads s global g (scalarStep candidate t space i state).events) :
    DataInvariant s global g (scalarStep candidate t space i state).state ∧ Stores s global g (scalarStep candidate t space i state).events := by
  let a := {(state.lanes t).scalar with memory := arena state space}
  have old : Data s global (thread s g t) a := data_memory (inv t) _
  have fetched : (Dense.Compact.program s)[a.pc]?=some (.localStep i) ∨ ∃ sp, (Dense.Compact.program s)[a.pc]?=some (.memory sp i) := by
    cases space with
    | none => exact .inl fetch
    | some sp => exact .inr ⟨sp,fetch⟩
  cases ev : Scalar.eval candidate i a with
  | next next occ =>
    dsimp only [a] at ev
    have readValues : ∀ effect, occ.memory=some effect → effect.kind=.load → ReadData s global (thread s g t) occ.pc effect.value := by
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
    have data := Dense.Compact.scalar_data s b.arithmetic global (thread s g t) a next i occ old fetched ev readValues
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
      exact Dense.Compact.scalar_store_data s global (thread s g owner) a next i seen _ effect old fetch ev memory store
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

theorem dispatch_data (s : Dense.Shape) (b : Bounds s) (global : List Word) (g : Fin s.rows)
    {state : Parallel.State s.width} {candidate : Option Word} {t : Fin s.width} {i : Instr} {out : Outcome s.width} (step : Dispatch ((config s b).group g) candidate t i state out)
    (fetch : (Dense.Compact.program s)[(state.lanes t).scalar.pc]?=some i)
    (inv : DataInvariant s global g state) (aligned : Aligned state) (reads : Reads s global g out.events) :
    DataInvariant s global g out.state ∧ Stores s global g out.events := by
  cases step with
  | localStep => exact scalar_machine s b global g state t none _ inv fetch reads
  | memory => exact scalar_machine s b global g state t (some _) _ inv fetch reads
  | binary32 ev =>
    refine ⟨install inv t _ (Dense.Compact.fp_data s global (thread s g t) _ _ _ _ (inv t) fetch ev),?_⟩
    intro owner space occ effect member; simp at member
  | exit =>
    refine ⟨install inv t _ (inv t),?_⟩
    intro owner space occ effect member; simp at member
  | sync =>
    rename_i resource
    cases hd : (Barrier.step (barrierConfig ((config s b).group g) state t) state.barrier (barrierRequest ((config s b).group g) state t resource)).disposition with
    | rejectedWrongKey =>
      refine ⟨by simpa [synchronize,hd] using inv,?_⟩
      intro owner space occ effect member; simp [synchronize,hd] at member
    | waiting =>
      refine ⟨by simpa [synchronize,hd,DataInvariant] using inv,?_⟩
      intro owner space occ effect member; simp [synchronize,hd] at member
    | released =>
      have pcs := release_aligned ((config s b).group g) state t resource aligned hd
      constructor
      · intro u
        simpa [synchronize,hd] using Dense.Compact.barrier_data s global (thread s g u) (state.lanes u).scalar resource (inv u) (by rw [pcs]; exact fetch)
      · intro owner space occ effect member; simp [synchronize,hd] at member

theorem step_data (s : Dense.Shape) (b : Bounds s) (global : List Word) (g : Fin s.rows)
    {state : Parallel.State s.width} {candidate : Option Word} {t : Fin s.width} {out : Outcome s.width} (step : Step ((config s b).group g) (Dense.Compact.program s) candidate t state out)
    (inv : DataInvariant s global g state) (aligned : Aligned state) (reads : Reads s global g out.events) :
    DataInvariant s global g out.state ∧ Stores s global g out.events := by
  have h := step.2
  split at h
  · subst out; exact ⟨inv,by intro _ _ _ _ member; simp at member⟩
  · split at h
    · subst out; exact ⟨inv,by intro _ _ _ _ member; simp at member⟩
    · split at h
      · subst out; exact ⟨inv,by intro _ _ _ _ member; simp at member⟩
      · exact dispatch_data s b global g h (by assumption) inv aligned reads

end Ptx.Scalar.Parallel.GridDense.LocalData

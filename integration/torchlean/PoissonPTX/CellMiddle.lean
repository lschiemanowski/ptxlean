import PoissonPTX.ConcurrentAddress
import PoissonPTX.ConcurrentPadding
import PoissonPTX.ContractionText

/-! Exact middle arithmetic phases, after gather and before final output.
Inputs are the actual starting register/byte state, not presumed tensor answers. -/
namespace PtxTorchLean.Poisson.PTX.Concurrent.CellMiddle
open Ptx

def planeOffset (width p : Nat) : Word := BitVec.ofNat 64 (p*width*width*8)

def dot (width acc : Nat) (a b : Contraction.Matrix) : List Op :=
  Contraction.program width acc a b

def weighted (w : Word) : List Op :=
  [.wide8 1 (.reg 14),.add64 2 (.reg 0) (.reg 1),.add64 2 (.reg 2) (.imm w),
   .load64 .global 6 (.reg 2),.fp .mul 8 (.reg 8) (.reg 6)]

def first (width : Nat) (b d : Word) : List Op :=
  dot width 8 ⟨.global,b,.row,.inner⟩ ⟨.shared,planeOffset width 0,.inner,.column⟩ ++
    SharedStore.code (planeOffset width 1) 8 ++
  dot width 8 ⟨.global,d,.row,.inner⟩ ⟨.shared,planeOffset width 0,.inner,.column⟩ ++
    SharedStore.code (planeOffset width 2) 8

def second (width : Nat) (b d w : Word) : List Op :=
  dot width 8 ⟨.shared,planeOffset width 1,.row,.inner⟩ ⟨.global,d,.column,.inner⟩ ++
    weighted w ++ SharedStore.code (planeOffset width 3) 8 ++
  dot width 8 ⟨.shared,planeOffset width 2,.row,.inner⟩ ⟨.global,b,.column,.inner⟩ ++
    weighted w ++ SharedStore.code (planeOffset width 4) 8

def third (width : Nat) (b d : Word) : List Op :=
  dot width 8 ⟨.global,b,.inner,.row⟩ ⟨.shared,planeOffset width 3,.inner,.column⟩ ++
    SharedStore.code (planeOffset width 5) 8 ++
  dot width 8 ⟨.global,d,.inner,.row⟩ ⟨.shared,planeOffset width 4,.inner,.column⟩ ++
    SharedStore.code (planeOffset width 6) 8

def phase (active start : Nat) (body : List Op) : List Instr :=
  [.skip active (start+1+body.length)] ++ body.map Instr.data ++ [.sync 0]

def code (width : Nat) (b d w : Word) : List Instr :=
  let a := first width b d
  let c := second width b d w
  phase (width*width) 0 a ++ phase (width*width) (a.length+2) c ++
    phase (width*width) (a.length+c.length+4) (third width b d)

/-- Missing plane zero is input to this slice; its sentinel site is the first
guard, distinct from every actual store. -/
def site (program : List Instr) (width : Nat) (p : Fin 7) : Nat :=
  if p=0 then 0 else program.findIdx fun i =>
    match i with
    | .data (.store64 .shared (.offset 2 off) _) => off == planeOffset width p.val
    | _ => false

/-- Per-instruction structural checks are finite and executable. No memory
value, tensor result, or read-source assignment is checked here. -/
def checkAt (program : List Instr) (width pc : Nat) (i : Instr) : Prop :=
  match i with
  | .data op => SharedStore.keeps 3 op ∧ SharedStore.keeps 14 op ∧
      match op with
      | .store64 .shared addr _ => ∃ p : Fin 7,
          pc=site program width p ∧ addr=.offset 2 (planeOffset width p.val) ∧
          Address.tag program pc=.addressed
      | _ => True
  | .skip active target => active=width*width ∧ pc<target ∧
      Address.tag program target=.none ∧ Padding.outside program target=true
  | .sync resource => resource=0 ∧ Padding.outside program (pc+1)=true

instance : Decidable (checkAt program width pc i) := by
  unfold checkAt
  split
  · cases ‹Op› <;> simp only [SharedStore.keeps] <;> try exact inferInstance
    cases ‹Space› <;> exact inferInstance
  · exact inferInstance
  · exact inferInstance

def Checked (program : List Instr) (width : Nat) : Prop :=
  ∀ pc : Fin program.length, checkAt program width pc.val program[pc.val]

instance : Decidable (Checked program width) :=
  inferInstanceAs (Decidable (∀ pc : Fin program.length, checkAt program width pc.val program[pc.val]))

theorem checked_at (checked : Checked program width) (fetch : program[pc]?=some i) :
    checkAt program width pc i := by
  obtain ⟨hp,he⟩ := List.getElem?_eq_some_iff.mp fetch
  simpa [he] using checked ⟨pc,hp⟩

theorem checked_keeps (checked : Checked program width) :
    Address.Keeps program 3 ∧ Address.Keeps program 14 := by
  constructor <;> intro pc op fetch
  · exact (checked_at checked fetch).1
  · exact (checked_at checked fetch).2.1

theorem checked_entries (checked : Checked program width) : Address.Entries program := by
  intro pc active target fetch
  exact (checked_at checked fetch).2.2.1

theorem checked_forward (checked : Checked program width) : Forward program := by
  intro pc active target fetch
  exact (checked_at checked fetch).2.1

theorem checked_boundaries (checked : Checked program width) : Padding.Boundaries program (width*width) := by
  constructor
  · intro pc active target fetch
    have h := checked_at checked fetch
    exact ⟨h.1,h.2.2.2⟩
  · intro pc resource fetch
    exact (checked_at checked fetch).2

theorem checked_writer_stops (checked : Checked program width) (live : thread.val<width*width) :
    StopsFor program thread pc := by
  intro atPC count target fetch before
  have countEq := (checked_at checked fetch).1
  exact Or.inl (by omega)

/-- Actual fetched stores satisfy plane coverage once the finite structural
check and initial lane/base registers are established. No address or value
coverage premise is supplied for the execution. -/
theorem plane_stores {start : State n} {events : List (Event n)}
    (run : Runs cfg program start events final) (checked : Checked program width)
    (reset : start.barrier=Barrier.reset generation)
    (pcs : ∀ t, (start.lanes t).pc=0) (outside : Padding.outside program 0=true)
    (bases : ∀ t, ((start.lanes t).regs 3).toNat=base)
    (lanes : ∀ t, ((start.lanes t).regs 14).toNat=t.val)
    (widthBound : width≤5) (fits : base+7*width*width*8≤2^64) :
    PlaneStores events base width (site program width) := by
  have aligned : Aligned start := by intro t h; simp [reset,Barrier.reset] at h
  have ready : Address.Invariant program start := by
    intro t; rw [pcs t,Address.tag_zero]; trivial
  have padding : Padding.Invariant program (width*width) start := by
    intro t inactive; simpa [pcs t] using outside
  obtain ⟨keepBase,keepLane⟩ := checked_keeps checked
  intro index thread access observed write shared
  have member := List.mem_of_getElem? observed
  have active := Padding.access_active run aligned padding (checked_boundaries checked) member
  obtain ⟨before,earlier,selected,out,suffix,hp,hs,hm,ht,he⟩ := run_access_prefix run member
  obtain ⟨eq,op,next,fetch,hd⟩ := step_access_origin hs hm
  subst selected
  obtain ⟨sp,addr,src,rfl,record,valid,result⟩ := store_origin hd write
  have spaceEq : sp=.shared := by rw [record] at shared; exact shared
  subst sp
  obtain ⟨p,pc,ea,tagged⟩ := (checked_at checked fetch).2.2
  subst addr
  have prepared := Address.runs_invariant hp aligned ready (checked_entries checked) keepBase keepLane thread
  rw [tagged] at prepared
  have b : ((before.lanes thread).regs 3).toNat=base := by
    rw [Address.runs_keeps hp keepBase thread]; exact bases thread
  have l : ((before.lanes thread).regs 14).toNat=thread.val := by
    rw [Address.runs_keeps hp keepLane thread]; exact lanes thread
  refine ⟨p,active,?_,?_⟩
  · simpa [record] using pc
  · rw [record]
    change ((before.lanes thread).regs 2+planeOffset width p.val).toNat=_
    change (before.lanes thread).regs 2=(before.lanes thread).regs 3+wide (before.lanes thread) 14 at prepared
    rw [prepared]
    exact SharedPlane.store_address (before.lanes thread) base width p ⟨thread.val,active⟩ widthBound b l fits

/-- Render these exact three phase bodies; the frontend binds guard/barrier
positions separately to the same instruction layout. -/
def rendered (width : Nat) (b d w : Word) : List (List String) :=
  [first width b d,second width b d w,third width b d].map (List.map Contraction.render)

end PtxTorchLean.Poisson.PTX.Concurrent.CellMiddle

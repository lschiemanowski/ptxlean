import PoissonPTX.CellMiddle

/-! Kernel-checked structural certificates for the four emitted middle-phase
layouts. The frontend requires these offsets; other layouts need a certificate. -/
namespace PtxTorchLean.Poisson.PTX.Concurrent.CellMiddle.Checks
open Ptx
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

def derivativeOffset (width : Nat) : Word := BitVec.ofNat 64 (width*width*8+32)
def weightOffset (width : Nat) : Word := BitVec.ofNat 64 (2*(width*width*8+32))
def program (width : Nat) : List Instr := code width 0 (derivativeOffset width) (weightOffset width)

theorem q1 : Checked (program 2) 2 := by decide +kernel
theorem q2 : Checked (program 3) 3 := by decide +kernel
theorem q3 : Checked (program 4) 4 := by decide +kernel
theorem q4 : Checked (program 5) 5 := by decide +kernel

theorem checked (width : Nat) (lo : 2≤width) (hi : width≤5) : Checked (program width) width := by
  interval_cases width
  · exact q1
  · exact q2
  · exact q3
  · exact q4

theorem sites_injective (width : Nat) (lo : 2≤width) (hi : width≤5) :
    Function.Injective (site (program width) width) := by
  interval_cases width <;> decide +kernel

def boundary (width : Nat) (phase : Fin 3) : Nat :=
  let a := (first width 0 (derivativeOffset width)).length
  let b := (second width 0 (derivativeOffset width) (weightOffset width)).length
  if phase=0 then a+1 else if phase=1 then a+b+3 else (program width).length-1

def preceding (plane : Fin 7) : Fin 3 :=
  if plane.val≤2 then 0 else if plane.val≤4 then 1 else 2

/-- Check all branch targets relative to one boundary, over actual instructions. -/
def Bounded (code : List Instr) (bound : Nat) : Prop :=
  ∀ pc : Fin code.length, match code[pc.val] with
    | .skip _ target => pc.val≤bound → target≤bound
    | _ => True

instance {code : List Instr} : Decidable (Bounded code bound) := by
  unfold Bounded
  letI : (pc : Fin code.length) → Decidable (match code[pc.val] with
    | .skip _ target => pc.val≤bound → target≤bound
    | _ => True) := fun pc => by split <;> infer_instance
  exact inferInstance

theorem bounded_stops {code : List Instr} (h : Bounded code bound) : StopsAt code bound := by
  intro pc count target fetch before
  obtain ⟨hp,he⟩ := List.getElem?_eq_some_iff.mp fetch
  have hh := h ⟨pc,hp⟩
  simp only [he] at hh
  exact hh before

theorem boundaries (width : Nat) (lo : 2≤width) (hi : width≤5) :
    ∀ phase : Fin 3, (program width)[boundary width phase]?=some (.sync 0) ∧
      Bounded (program width) (boundary width phase) := by
  interval_cases width <;> decide +kernel

theorem stores (width : Nat) (lo : 2≤width) (hi : width≤5) :
    ∀ p : Fin 7, p≠0 →
      (program width)[site (program width) width p]?=
        some (.data (.store64 .shared (.offset 2 (planeOffset width p.val)) (.reg 8))) ∧
      site (program width) width p < boundary width (preceding p) := by
  interval_cases width <;> decide +kernel

/-- Every shared store in every candidate execution of a certified middle slice
has its lane's plane address. Initial input bytes and candidate values are free. -/
theorem coverage {start : State 32} (width : Nat) (lo : 2≤width) (hi : width≤5)
    (run : Runs cfg (program width) start events final)
    (reset : start.barrier=Barrier.reset generation)
    (pcs : ∀ t, (start.lanes t).pc=0)
    (bases : ∀ t, ((start.lanes t).regs 3).toNat=base)
    (lanes : ∀ t, ((start.lanes t).regs 14).toNat=t.val)
    (fits : base+7*width*width*8≤2^64) :
    PlaneStores events base width (site (program width) width) := by
  apply plane_stores run (checked width lo hi) reset pcs _ bases lanes hi fits
  simp [Padding.outside,program,code,phase]

theorem unique {start : State 32} {events : List (Event 32)} {index : Nat}
    (width : Nat) (lo : 2≤width) (hi : width≤5)
    (run : Runs cfg (program width) start events final)
    (reset : start.barrier=Barrier.reset generation) (pcs : ∀ t, (start.lanes t).pc=0)
    (bases : ∀ t, ((start.lanes t).regs 3).toNat=base)
    (lanes : ∀ t, ((start.lanes t).regs 14).toNat=t.val)
    (fits : base+7*width*width*8≤2^64)
    (observed : events[index]?=some (.data thread access))
    (store : access.data.store=true) (shared : access.space=.shared) :
    Visibility.SoleWriter events index access.data.address :=
  plane_sole_writer run (checked_forward (checked width lo hi))
    (coverage width lo hi run reset pcs bases lanes fits) observed store shared

/-- A later read of an intermediate plane must recover the actual producer's
stored word. Ordering and store-address coverage are both derived for the
certified concrete program, not supplied as execution assumptions. -/
theorem publication {start : State 32} {events : List (Event 32)} {index : Nat}
    (width : Nat) (lo : 2≤width) (hi : width≤5)
    (run : Runs cfg (program width) start events final)
    (reset : start.barrier=Barrier.reset generation) (pcs : ∀ t, (start.lanes t).pc=0)
    (bases : ∀ t, ((start.lanes t).regs 3).toNat=base)
    (lanes : ∀ t, ((start.lanes t).regs 14).toNat=t.val)
    (fits : base+7*width*width*8≤2^64)
    (plane : Fin 7) (produced : plane≠0) (writer : Fin 32) (active : writer.val<width*width)
    (observed : events[index]?=some (.data reader access))
    (later : boundary width (preceding plane)<access.data.pc)
    (read : access.data.store=false) (shared : access.space=.shared)
    (address : access.data.address=SharedPlane.address base width plane.val writer.val)
    (compatible : Visibility.Compatible initialBytes events source)
    (performed : Visibility.Performed events source) :
    ∃ w wa, events[w]?=some (.data writer wa) ∧
      access.data.value=wa.data.value ∧ ∀ k, source index k=.store w k := by
  obtain ⟨fetch,before⟩ := stores width lo hi plane produced
  obtain ⟨barrier,stops⟩ := boundaries width lo hi (preceding plane)
  obtain ⟨w,wa,hw,pc,across,value,bytes⟩ := read_from_plane_producer run reset
    (checked_forward (checked width lo hi)) (coverage width lo hi run reset pcs bases lanes fits)
    (sites_injective width lo hi) plane fetch (checked_writer_stops (checked width lo hi) active)
    (by rw [pcs]; omega) before barrier (bounded_stops stops)
    (by intro t; rw [pcs]; omega) observed later read shared address compatible performed
  exact ⟨w,wa,hw,value,bytes⟩

/-- Corrupting the actual lane-scaling instruction breaks address readiness. -/
theorem wrong_scale_rejected :
    ¬Checked [.data (.wide8 1 (.imm 0)),.data (.add64 2 (.reg 3) (.reg 1)),
      .data (.store64 .shared (.offset 2 32) (.reg 8))] 2 := by decide +kernel

/-- Entering halfway through address preparation is not a valid certificate. -/
theorem jump_into_store_rejected :
    ¬Checked [.skip 4 3,.data (.wide8 1 (.reg 14)),.data (.add64 2 (.reg 3) (.reg 1)),
      .data (.store64 .shared (.offset 2 32) (.reg 8)),.sync 0] 2 := by decide +kernel

end PtxTorchLean.Poisson.PTX.Concurrent.CellMiddle.Checks

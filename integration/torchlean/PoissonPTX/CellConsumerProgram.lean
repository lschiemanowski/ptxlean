import PoissonPTX.CellFinalSnapshot
import PoissonPTX.ConcurrentExtension

/-! Middle phases followed by the active final arithmetic in the same concurrent
machine. Index/store/return still use the separate fetched Kernel model. -/
namespace PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer
open Ptx CellMiddle Symbolic
set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

def body (width : Nat) : List Op := CellFinal.arithmetic width 0 (Checks.derivativeOffset width)
def suffix (width : Nat) : List Instr :=
  [.skip (width*width) ((Checks.program width).length+1+(body width).length)]++(body width).map .data
def program (width : Nat) : List Instr := Checks.program width++suffix width

theorem checked (width : Nat) (lo : 2≤width) (hi : width≤5) : Checked (program width) width := by
  interval_cases width <;> decide +kernel

theorem shared_stores (width : Nat) (lo : 2≤width) (hi : width≤5) : Inputs.SharedStores (program width) := by
  interval_cases width <;> decide +kernel

theorem sites (width : Nat) (lo : 2≤width) (hi : width≤5) :
    ∀ p : Fin 7, site (program width) width p=site (Checks.program width) width p := by
  interval_cases width <;> decide +kernel

theorem boundaries (width : Nat) (lo : 2≤width) (hi : width≤5) :
    ∀ phase : Fin 3, (program width)[Checks.boundary width phase]?=some (.sync 0) ∧
      Checks.Bounded (program width) (Checks.boundary width phase) := by
  interval_cases width <;> decide +kernel

theorem stores (width : Nat) (lo : 2≤width) (hi : width≤5) :
    ∀ p : Fin 7, p≠0 →
      (program width)[site (program width) width p]?=
        some (.data (.store64 .shared (.offset 2 (planeOffset width p.val)) (.reg 8))) ∧
      site (program width) width p < Checks.boundary width (Checks.preceding p) := by
  interval_cases width <;> decide +kernel

theorem no_tail_stores (width : Nat) (lo : 2≤width) (hi : width≤5) :
    ∀ pc : Fin (program width).length, (Checks.program width).length≤pc.val →
      (match (program width)[pc.val] with
      | .data op => Replay.noStore op
      | _ => true)=true := by
  interval_cases width <;> decide +kernel

def expected (width lane : Nat) : Number :=
  let g offset i j := Numeric.entry width .global offset i j
  let s p i j := Numeric.entry width .shared (p*width*width*8) i j
  .fp .add
    (Numeric.sum width (fun k => s 5 (lane/width) k) (fun k => g (width*width*8+32) k (lane%width)))
    (Numeric.sum width (fun k => s 6 (lane/width) k) (fun k => g 0 k (lane%width)))

def Results (width : Nat) : Prop := ∀ lane : Fin (width*width),
  number (atPC .values (program width) (Numeric.seed width lane.val) (program width).length 11)=some (expected width lane.val)
instance : Decidable (Results width) := by unfold Results; infer_instance

theorem results (width : Nat) (lo : 2≤width) (hi : width≤5) : Results width := by
  interval_cases width <;> decide +kernel

/-- This certificate describes final loads by address, never by their values. -/
def loadCheck (width lane pc : Nat) : Prop :=
  match (program width)[pc]? with
  | some (.data (.load64 sp _ addr)) =>
    match Numeric.extract (operand (atPC .addresses (program width) (Numeric.seed width lane) pc) addr) with
    | none => False
    | some (space,off) => sp=space ∧ off.toNat%8=0 ∧
      (sp=.shared → off.toNat<7*width*width*8 ∧
        (off.toNat/(width*width*8)=5 ∨ off.toNat/(width*width*8)=6) ∧
        Checks.boundary width 2<pc)
  | _ => True
instance : Decidable (loadCheck width lane pc) := by
  unfold loadCheck; split
  · split <;> infer_instance
  · infer_instance

def Loads (width : Nat) : Prop := ∀ lane : Fin (width*width), ∀ pc : Fin (program width).length,
  (Checks.program width).length≤pc.val → loadCheck width lane.val pc.val
instance : Decidable (Loads width) := by unfold Loads; infer_instance

theorem loads (width : Nat) (lo : 2≤width) (hi : width≤5) : Loads width := by
  interval_cases width <;> decide +kernel

end PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer

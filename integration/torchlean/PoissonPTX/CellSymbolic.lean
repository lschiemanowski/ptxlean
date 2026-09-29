import PoissonPTX.SymbolicRun
import PoissonPTX.CellMiddleInputs

namespace PtxTorchLean.Poisson.PTX.Concurrent.CellMiddle.Numeric
open Symbolic Checks
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

def seed (width lane : Nat) : Symbolic.Registers := fun r =>
  if r=0 then .bits (.base .global) else
  if r=3 then .bits (.base .shared) else
  if r=14 then .bits (.literal (BitVec.ofNat 64 lane)) else
  if r=16 then .bits (.literal (BitVec.ofNat 64 (lane/width))) else
  if r=17 then .bits (.literal (BitVec.ofNat 64 (lane%width))) else .unknown

def address (sp : Space) (offset : Nat) : Bits := Symbolic.add (.base sp) (.literal (BitVec.ofNat 64 offset))

def extract : Value → Option (Space × Word)
  | .bits (.base sp) => some (sp,0)
  | .bits (.add (.base sp) (.literal off)) => some (sp,off)
  | _ => none

theorem extract_sound (related : Symbolic.Rel bases memory v word) (h : extract v=some (sp,off)) :
    word=bases sp+off := by
  unfold extract at h
  split at h
  · obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Option.some.inj h)
    simpa [Symbolic.Rel,Bits.eval] using related
  · obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Option.some.inj h)
    exact related
  · cases h

def loadCheck (width lane pc : Nat) : Prop :=
  match (program width)[pc]? with
  | some (.data (.load64 sp _ addr)) =>
    match extract (operand (atPC .addresses (program width) (seed width lane) pc) addr) with
    | none => False
    | some (space,off) => sp=space ∧ off.toNat%8=0 ∧
      (sp=.shared → off.toNat<7*width*width*8 ∧
        (∀ p : Fin 7, off.toNat/(width*width*8)=p.val → p≠0 → boundary width (preceding p)<pc))
  | _ => True

instance : Decidable (loadCheck width lane pc) := by
  unfold loadCheck
  split
  · split
    · exact inferInstance
    · exact inferInstance
  · exact inferInstance

def Loads (width : Nat) : Prop :=
  ∀ lane : Fin (width*width), ∀ pc : Fin (program width).length, loadCheck width lane.val pc.val
instance : Decidable (Loads width) := inferInstanceAs (Decidable (∀ lane : Fin (width*width), ∀ pc : Fin (program width).length, loadCheck width lane.val pc.val))

/-- Byte-view entries with the generated row-major address calculation. -/
def entry (width : Nat) (sp : Space) (offset row col : Nat) : Number :=
  .bits (.load sp (address sp (offset+(row*width+col)*8)))

def sum (width : Nat) (a b : Nat → Number) : Number :=
  (List.range width).foldl (fun z k => .fp .add z (.fp .mul (a k) (b k))) (.bits (.literal 0))

def expected (width plane lane : Nat) : Number :=
  let row := lane/width
  let col := lane%width
  let g offset i j := entry width .global offset i j
  let s p i j := entry width .shared (p*width*width*8) i j
  let d := width*width*8+32
  let w := 2*(width*width*8+32)
  match plane with
  | 1 => sum width (fun k => g 0 row k) (fun k => s 0 k col)
  | 2 => sum width (fun k => g d row k) (fun k => s 0 k col)
  | 3 => .fp .mul (sum width (fun k => s 1 row k) (fun k => g d col k)) (g w row col)
  | 4 => .fp .mul (sum width (fun k => s 2 row k) (fun k => g 0 col k)) (g w row col)
  | 5 => sum width (fun k => g 0 k row) (fun k => s 3 k col)
  | _ => sum width (fun k => g d k row) (fun k => s 4 k col)

def Stores (width : Nat) : Prop :=
  ∀ lane : Fin (width*width), ∀ p : Fin 6,
    number (atPC .values (program width) (seed width lane.val)
      (site (program width) width ⟨p.val+1,by omega⟩) 8)=some (expected width (p.val+1) lane.val)
instance : Decidable (Stores width) := by unfold Stores; infer_instance

theorem loads_q1 : Loads 2 := by decide +kernel
theorem loads_q2 : Loads 3 := by decide +kernel
theorem loads_q3 : Loads 4 := by decide +kernel
theorem loads_q4 : Loads 5 := by decide +kernel

theorem stores_q1 : Stores 2 := by decide +kernel
theorem stores_q2 : Stores 3 := by decide +kernel
theorem stores_q3 : Stores 4 := by decide +kernel
theorem stores_q4 : Stores 5 := by decide +kernel

theorem loads (width : Nat) (lo : 2≤width) (hi : width≤5) : Loads width := by
  interval_cases width
  · exact loads_q1
  · exact loads_q2
  · exact loads_q3
  · exact loads_q4

theorem stores (width : Nat) (lo : 2≤width) (hi : width≤5) : Stores width := by
  interval_cases width
  · exact stores_q1
  · exact stores_q2
  · exact stores_q3
  · exact stores_q4

end PtxTorchLean.Poisson.PTX.Concurrent.CellMiddle.Numeric

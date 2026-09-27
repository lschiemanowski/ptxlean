import PtxBinary32.MaximumProgram

/-! Register liveness contracts for the actual maximum program. A condition is
required only between the fetched instruction that creates a value and its use. -/
namespace Ptx.Scalar.Parallel.Maximum
open Ptx.Binary32.Maximum
abbrev node (global : List Word) (k t : Nat) := Tree.nodeValue (fun i => global[i]!) k t

structure Data (d : Nat) (global : List Word) (t : Fin (width d)) (a : Scalar.State) : Prop where
  tid : a.regs 0=BitVec.ofNat 32 t.val
  publication : 4≤a.pc → a.pc≤5 → a.regs 4=global[t.val]!
  roundGate : ∀ k<d, 6+24*k+1≤a.pc → a.pc≤6+24*k+23 → a.preds 0=decide (t.val<2^(d-(k+1)))
  left : ∀ k<d, 6+24*k+8≤a.pc → a.pc≤6+24*k+18 → t.val<2^(d-(k+1)) → a.regs 4=node global k (2*t.val)
  right : ∀ k<d, 6+24*k+9≤a.pc → a.pc≤6+24*k+18 → t.val<2^(d-(k+1)) → a.regs 5=node global k (2*t.val+1)
  leftSign : ∀ k<d, 6+24*k+10≤a.pc → a.pc≤6+24*k+11 → a.preds 1=decide ((a.regs 4).toNat≥2147483648)
  leftRaw : ∀ k<d, a.pc=6+24*k+11 → a.regs 8=a.regs 4 ^^^ 0x80000000
  leftKey : ∀ k<d, 6+24*k+12≤a.pc → a.pc≤6+24*k+18 → a.regs 8=key (a.regs 4)
  rightSign : ∀ k<d, 6+24*k+13≤a.pc → a.pc≤6+24*k+14 → a.preds 1=decide ((a.regs 5).toNat≥2147483648)
  rightRaw : ∀ k<d, a.pc=6+24*k+14 → a.regs 9=a.regs 5 ^^^ 0x80000000
  rightKey : ∀ k<d, 6+24*k+15≤a.pc → a.pc≤6+24*k+18 → a.regs 9=key (a.regs 5)
  compare : ∀ k<d, 6+24*k+16≤a.pc → a.pc≤6+24*k+17 → a.preds 1=decide ((key (a.regs 4)).toNat<(key (a.regs 5)).toNat)
  selectedLeft : ∀ k<d, a.pc=6+24*k+17 → a.regs 6=a.regs 4
  reduced : ∀ k<d, 6+24*k+18≤a.pc → a.pc≤6+24*k+23 → t.val<2^(d-(k+1)) → a.regs 6=node global (k+1) t.val
  outputGate : 6+24*d+1≤a.pc → a.pc≤6+24*d+11 → a.preds 0=decide (t.val=0)
  root : 6+24*d+6≤a.pc → a.pc≤6+24*d+11 → t.val=0 → a.regs 6=node global d 0

def ReadData (d : Nat) (global : List Word) (t : Fin (width d)) (pc : Nat) (value : Word) : Prop :=
  (pc=3 → value=global[t.val]!) ∧
  (∀ k<d, pc=6+24*k+7 → value=node global k (2*t.val)) ∧
  (∀ k<d, pc=6+24*k+8 → value=node global k (2*t.val+1)) ∧
  (pc=6+24*d+5 → value=node global d 0)

def StoreData (d : Nat) (global : List Word) (t : Fin (width d)) (pc : Nat) (value : Word) : Prop :=
  (pc=4 → value=global[t.val]!) ∧
  (∀ k<d, pc=6+24*k+22 → value=node global (k+1) t.val) ∧
  (pc=6+24*d+10 → value=node global d 0)

theorem initial_data (d : Nat) (global shared : List Word) (seeds : Fin (width d)→Scalar.State) (t : Fin (width d)) :
    Data d global t ((initial d global shared seeds).lanes t).scalar := by
  constructor <;> simp [initial,Scalar.update]
end Ptx.Scalar.Parallel.Maximum

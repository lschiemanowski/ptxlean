import PoissonPTX.Bytes
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-! Necessary byte-source constraints, deliberately weaker than full PTX
admission. Physical addresses use the identity/no-alias convention of this slice.
No uniform source, global order, read value, or correct computation is assumed. -/
namespace PtxTorchLean.Poisson.PTX.Sources

structure Access where
  pc : Nat
  store : Bool
  address : Nat
  value : Word
  deriving DecidableEq, Repr

/-- Each byte may choose a different actual store, or the initial byte. The
source byte offset is explicit, so partial overlap is not hidden by word indices. -/
inductive Origin (ι : Type) where
  | initial
  | store (event : ι) (offset : Fin 8)
  deriving DecidableEq, Repr

/-- Initial values are input bytes; program-store values come from the executed
access list. This is a necessary source condition, not complete memory admission. -/
def Compatible (initial : Memory) (events : ι → Access)
    (source : ι → Fin 8 → Origin ι) : Prop :=
  ∀ r, (events r).store = false → ∀ k,
    match source r k with
    | .initial => byte (events r).value k.val = initial ((events r).address+k.val)
    | .store w j => (events w).store = true ∧
        (events w).address+j.val = (events r).address+k.val ∧
        byte (events r).value k.val = byte (events w).value j.val

def ReadOnly (events : ι → Access) (address : Nat) : Prop :=
  ∀ w, (events w).store = true → ∀ j k : Fin 8,
    (events w).address+j.val ≠ address+k.val

theorem word_eq_of_bytes (a b : Word) (h : ∀ k : Fin 8, byte a k.val = byte b k.val) : a=b := by
  let m : Memory := fun _ => 0
  have same : write64 m 0 a = write64 m 0 b := by
    funext p
    by_cases hp : p < 8
    · simp [write64, hp, h ⟨p, hp⟩]
    · simp [write64, hp]
  calc
    a = read64 (write64 m 0 a) 0 := (read64_write64 m 0 a).symm
    _ = read64 (write64 m 0 b) 0 := congrArg (fun mem => read64 mem 0) same
    _ = b := read64_write64 m 0 b

@[simp] theorem byte_read64 (m : Memory) (a : Nat) (k : Fin 8) :
    byte (read64 m a) k.val = m (a+k.val) := by
  fin_cases k <;> simp [byte,read64] <;> bv_decide

/-- Read-only bytes force initialization as source, even when sources can tear. -/
theorem read_only_initial (compatible : Compatible initial events source)
    (hr : (events r).store = false) (ro : ReadOnly events (events r).address) :
    ∀ k, source r k = .initial := by
  intro k
  have h := compatible r hr k
  cases hs : source r k with
  | initial => rfl
  | store w j =>
    simp only [hs] at h
    exact False.elim (ro w h.1 j k h.2.1)

theorem read_only_value (compatible : Compatible initial events source)
    (hr : (events r).store = false) (ro : ReadOnly events (events r).address) :
    (events r).value = read64 initial (events r).address := by
  apply word_eq_of_bytes
  intro k
  have h := compatible r hr k
  rw [read_only_initial compatible hr ro k] at h
  simpa using h

/-- Separation concerns physical byte ranges, not just different base addresses. -/
def Disjoint (a b : Nat) : Prop := a+8 ≤ b ∨ b+8 ≤ a

theorem readonly_of_disjoint
    (h : ∀ w, (events w).store = true → Disjoint (events w).address address) :
    ReadOnly events address := by
  intro w hw j k
  have hd:=h w hw; have hj:=j.isLt; have hk:=k.isLt
  unfold Disjoint at hd
  omega

end PtxTorchLean.Poisson.PTX.Sources

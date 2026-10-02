import PoissonPTX.Bytes32
import PoissonPTX.ConcurrentReadOnly

namespace PtxTorchLean.Poisson.PTX.IndexSources
open Concurrent

/-- Only unsigned global four-byte reads are added. The existing chronological
word/barrier history retains every store; index reads cannot publish bytes. -/
structure Access where
  pc : Nat
  address : Nat
  value : BitVec 32
  deriving DecidableEq, Repr

def byte32 (word : BitVec 32) (k : Nat) : Byte := word.extractLsb' (8*k) 8

theorem byte_read32 (memory : Memory) (address : Nat) (k : Fin 4) :
    byte32 (read32 memory address) k.val=memory (address+k.val) := by
  fin_cases k <;> simp [byte32,read32] <;> bv_decide

theorem word_eq_of_bytes (a b : BitVec 32)
    (equal : ∀ k : Fin 4, byte32 a k.val=byte32 b k.val) : a=b := by
  have same : write32 (fun _ => 0) 0 a=write32 (fun _ => 0) 0 b := by
    funext p
    by_cases inside : p<4
    · simpa [write32,inside,byte32] using equal ⟨p,inside⟩
    · simp [write32,inside]
  have result := congrArg (fun m => read32 m 0) same
  simpa using result

/-- Sources name actual eight-byte stores or initialization, per byte, without
assuming atomicity, a desired node index, or a total memory order. -/
def Compatible (initial : Memory) (events : List (Event n))
    (indices : List (Fin n × Access)) (source : Nat → Fin 4 → Sources.Origin Nat) : Prop :=
  ∀ r reader ra, indices[r]?=some (reader,ra) → ∀ k,
    match source r k with
    | .initial => byte32 ra.value k.val=initial (ra.address+k.val)
    | .store w j => ∃ writer wa, events[w]?=some (.data writer wa) ∧
        wa.data.store=true ∧ wa.space=.global ∧
        wa.data.address+j.val=ra.address+k.val ∧
        byte32 ra.value k.val=byte wa.data.value j.val

def ReadOnly (events : List (Event n)) (address : Nat) : Prop :=
  ∀ (w : Nat) writer wa, events[w]?=some (.data writer wa) → wa.data.store=true → wa.space=.global →
    ∀ (j : Fin 8) (k : Fin 4), wa.data.address+j.val≠address+k.val

theorem read_only_initial {r : Nat} {ra : Access} (compatible : Compatible initial events indices source)
    (observed : indices[r]?=some (reader,ra)) (readonly : ReadOnly events ra.address) :
    ∀ k, source r k=.initial := by
  intro k
  have h := compatible r reader ra observed k
  cases hs : source r k with
  | initial => rfl
  | store w j =>
    simp only [hs] at h
    obtain ⟨writer,wa,hw,store,space,address,_⟩ := h
    exact False.elim (readonly w writer wa hw store space j k address)

theorem read_only_value {r : Nat} {ra : Access} (compatible : Compatible initial events indices source)
    (observed : indices[r]?=some (reader,ra)) (readonly : ReadOnly events ra.address) :
    ra.value=read32 initial ra.address := by
  apply word_eq_of_bytes
  intro k
  have h := compatible r reader ra observed k
  rw [read_only_initial compatible observed readonly k] at h
  simpa only [byte_read32] using h

theorem readonly_of_disjoint {events : List (Event n)} {address : Nat}
    (apart : ∀ (w : Nat) writer wa, events[w]?=some (.data writer wa) →
      wa.data.store=true → wa.space=.global → wa.data.address+8≤address ∨ address+4≤wa.data.address) :
    ReadOnly events address := by
  intro w writer wa observed store global j k
  have h := apart w writer wa observed store global
  have := j.isLt; have := k.isLt; omega

theorem readonly_of_no_global_stores {events : List (Event n)} {address : Nat}
    (none : ∀ (w : Nat) writer wa, events[w]?=some (.data writer wa) →
      wa.data.store=true → wa.space≠.global) : ReadOnly events address := by
  intro w writer wa observed store global
  exact False.elim (none w writer wa observed store global)

end PtxTorchLean.Poisson.PTX.IndexSources

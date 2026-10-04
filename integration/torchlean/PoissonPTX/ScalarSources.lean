import PoissonPTX.IndexSources

namespace PtxTorchLean.Poisson.PTX.Scalar.Sources

/-- An actual access width, retained when flag and numerical operations share
one history. This does not model overlapping mixed-width accesses. -/
inductive Width where
  | flag | word
  deriving DecidableEq, Repr

def Width.bytes : Width → Nat | .flag => 4 | .word => 8

structure Access where
  pc : Nat
  store : Bool
  space : Space
  address : Nat
  width : Width
  value : Word
  deriving DecidableEq, Repr

def Access.byte (a : Access) (k : Nat) : Byte := PTX.byte a.value k

def word (a : Concurrent.Access) : Access := ⟨a.data.pc,a.data.store,a.space,a.data.address,.word,a.data.value⟩
def flag (pc : Nat) (store : Bool) (address : Nat) (value : BitVec 32) : Access :=
  ⟨pc,store,.global,address,.flag,value.setWidth 64⟩
def index (a : IndexSources.Access) : Access := flag a.pc false a.address a.value

/-- Each supplied byte names initialization or an actual store byte, with its
real width checked. No word value or tensor answer is a source premise. -/
def Compatible (initial : Space → Memory) (events : List Access)
    (source : Nat → Fin 8 → PTX.Sources.Origin Nat) : Prop :=
  ∀ r ra, events[r]?=some ra → ra.store=false → ∀ k : Fin 8, k.val<ra.width.bytes →
    match source r k with
    | .initial => ra.byte k.val=initial ra.space (ra.address+k.val)
    | .store w j => ∃ wa, events[w]?=some wa ∧ wa.store=true ∧ wa.space=ra.space ∧
        j.val<wa.width.bytes ∧ wa.address+j.val=ra.address+k.val ∧ ra.byte k.val=wa.byte j.val

/-- Necessary no-future-source rule for a single thread's synchronous generic,
non-aliasing accesses to the same address and width. The event list records
that thread's program order; this is not a cross-thread order or full admission. -/
def NoFuture (events : List Access) (source : Nat → Fin 8 → PTX.Sources.Origin Nat) : Prop :=
  ∀ r w ra wa, events[r]?=some ra → events[w]?=some wa → ra.store=false → wa.store=true →
    ra.space=wa.space → ra.address=wa.address → ra.width=wa.width → r<w →
    ∀ j k, source r k≠.store w j

/-- If every writer touching a read byte is a later same-width in-place write,
compatibility and no-future admission force that byte to come from initialization. -/
theorem initial_value (compatible : Compatible initial events source) (admitted : NoFuture events source)
    (found : events[r]?=some ra) (read : ra.store=false)
    (writers : ∀ w wa, events[w]?=some wa → wa.store=true → wa.space=ra.space →
      ∀ j k : Fin 8, j.val<wa.width.bytes → k.val<ra.width.bytes → wa.address+j.val=ra.address+k.val →
        r<w ∧ wa.address=ra.address ∧ wa.width=ra.width) :
    ∀ k : Fin 8, k.val<ra.width.bytes → source r k=.initial ∧ ra.byte k.val=initial ra.space (ra.address+k.val) := by
  intro k small
  have bytes := compatible r ra found read k small
  cases picked : source r k with
  | initial => exact ⟨rfl,by simpa only [picked] using bytes⟩
  | store w j =>
    rw [picked] at bytes
    obtain ⟨wa,stored,write,space,inside,same,_⟩ := bytes
    obtain ⟨later,address,width⟩ := writers w wa stored write space j k inside small same
    exact False.elim (admitted r w ra wa found stored read write space.symm address.symm width.symm later j k picked)

theorem initial_no_future : NoFuture events (fun _ _ => .initial) := by
  intro r w ra wa hr hw read write space address width later j k
  simp

theorem flag_byte (pc : Nat) (store : Bool) (address : Nat) (value : BitVec 32) (k : Fin 4) :
    (flag pc store address value).byte k.val=IndexSources.byte32 value k.val := by
  fin_cases k <;> simp [flag,Access.byte,PTX.byte,IndexSources.byte32] <;> bv_decide

theorem word_value (bytes : ∀ k : Fin 8, (word a).byte k.val=memory (a.data.address+k.val)) :
    a.data.value=read64 memory a.data.address := by
  apply PTX.Sources.word_eq_of_bytes
  intro k
  simpa only [word,Access.byte,PTX.Sources.byte_read64] using bytes k

theorem flag_value {pc address : Nat} {store : Bool} {value : BitVec 32} (bytes : ∀ k : Fin 4, (flag pc store address value).byte k.val=memory (address+k.val)) :
    value=read32 memory address := by
  apply IndexSources.word_eq_of_bytes
  intro k
  simpa only [flag_byte,IndexSources.byte_read32] using bytes k

end PtxTorchLean.Poisson.PTX.Scalar.Sources

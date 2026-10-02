import PoissonPTX.CellGrid

namespace PtxTorchLean.Poisson.PTX.CellGrid

/-- Sources name a block and an access in that block's actual projected history.
This retains event provenance without confusing equal local instruction counters
or equal shared addresses in different blocks. -/
abbrev Sources (count : Nat) := Fin count → Nat → Fin 8 → PTX.Sources.Origin (Fin count × Nat)

def initial (global : Memory) (shared : Fin count → Memory) (block : Fin count) : Space → Memory
  | .global => global
  | .shared => shared block

/-- Necessary byte-source constraints for the grid candidate execution. Shared
storage is block-private. This is not complete PTX memory-model admission. -/
def Compatible (global : Memory) (shared : Fin count → Memory) (events : List (Event count))
    (source : Sources count) : Prop :=
  ∀ block r reader ra, (forBlock block events)[r]?=some (.data reader ra) → ra.data.store=false → ∀ k,
    match source block r k with
    | .initial => byte ra.data.value k.val=initial global shared block ra.space (ra.data.address+k.val)
    | .store (writerBlock,w) j => ∃ writer wa,
        (forBlock writerBlock events)[w]?=some (.data writer wa) ∧ wa.data.store=true ∧
        byteAddress writerBlock wa.space (wa.data.address+j.val)=byteAddress block ra.space (ra.data.address+k.val) ∧
        byte ra.data.value k.val=byte wa.data.value j.val

/-- Source projection will use the original byte index and local event number.
Its soundness requires establishing that the writer is in this block. -/
def localSource (source : Sources count) (block : Fin count) (r : Nat) (k : Fin 8) : PTX.Sources.Origin Nat :=
  match source block r k with
  | .initial => .initial
  | .store (_,w) j => .store w j

/-- A geometry condition on actual accesses, to be discharged from the cell
input/output bounds. It does not prescribe a read value or computed result. -/
def NoForeignOverlap (events : List (Event count)) : Prop :=
  ∀ block other, block≠other → ∀ reader ra writer wa,
    .data reader ra∈forBlock block events → ra.data.store=false →
    .data writer wa∈forBlock other events → wa.data.store=true → ∀ j k : Fin 8,
    byteAddress other wa.space (wa.data.address+j.val)≠byteAddress block ra.space (ra.data.address+k.val)

variable {count : Nat} {global : Memory} {shared : Fin count → Memory}
  {events : List (Event count)} {source : Sources count}

/-- Even before global input/output separation, a shared read cannot name a
store in another block's private shared memory. -/
theorem shared_source_owner (compatible : Compatible global shared events source)
    (observed : (forBlock block events)[r]?=some (.data reader ra)) (read : ra.data.store=false)
    (space : ra.space=.shared) (chosen : source block r k=.store (writerBlock,w) j) : writerBlock=block := by
  have h := compatible block r reader ra observed read k
  rw [chosen] at h
  obtain ⟨writer,wa,found,store,address,value⟩ := h
  rw [space] at address
  cases ws : wa.space <;> simp [byteAddress,ws] at address
  exact address.1

/-- Actual separation makes every selected store source local. Reads may still
come from initialization, and the independent performed-write rule is retained. -/
theorem source_owner (compatible : Compatible global shared events source) (apart : NoForeignOverlap events)
    (observed : (forBlock block events)[r]?=some (.data reader ra)) (read : ra.data.store=false)
    (chosen : source block r k=.store (writerBlock,w) j) : writerBlock=block := by
  have h := compatible block r reader ra observed read k
  rw [chosen] at h
  obtain ⟨writer,wa,found,store,address,value⟩ := h
  by_contra different
  exact apart block writerBlock (Ne.symm different) reader ra writer wa
    (List.mem_of_getElem? observed) read (List.mem_of_getElem? found) store j k address

/-- Under proved access separation, projection recovers the original cell's
per-byte compatibility contract, not a supplied arithmetic answer. -/
theorem compatible_project (compatible : Compatible global shared events source)
    (apart : NoForeignOverlap events) (block : Fin count) :
    Concurrent.Visibility.Compatible (initial global shared block) (forBlock block events) (localSource source block) := by
  intro r reader ra observed read k
  have h := compatible block r reader ra observed read k
  cases chosen : source block r k with
  | initial => simpa [localSource,chosen] using h
  | store where_ j =>
    obtain ⟨writerBlock,w⟩ := where_
    have same := source_owner compatible apart observed read chosen
    subst writerBlock
    rw [chosen] at h
    obtain ⟨writer,wa,found,store,address,value⟩ := h
    simp only [localSource,chosen]
    refine ⟨writer,wa,found,store,?_,?_,value⟩
    · cases ws : wa.space <;> cases rs : ra.space <;> simp [byteAddress,ws,rs] at address ⊢
    · cases ws : wa.space <;> cases rs : ra.space <;> simpa [byteAddress,ws,rs] using address

/-- A shared store before the block's completed barrier cannot be bypassed by
initialization in a later overlapping shared read. This is the same necessary
performed-write condition as in the single-block fragment. -/
def Performed (events : List (Event count)) (source : Sources count) : Prop :=
  ∀ block w r writer reader wa ra,
    (forBlock block events)[w]?=some (.data writer wa) →
    (forBlock block events)[r]?=some (.data reader ra) →
    wa.data.store=true → ra.data.store=false → wa.space=.shared → ra.space=.shared →
    Concurrent.Visibility.Across (forBlock block events) w r → ∀ j k : Fin 8,
    wa.data.address+j.val=ra.data.address+k.val → source block r k≠.initial

theorem performed_project (performed : Performed events source) (block : Fin count) :
    Concurrent.Visibility.Performed (forBlock block events) (localSource source block) := by
  intro w r writer reader wa ra hw hr store read ws rs across j k same
  have required := performed block w r writer reader wa ra hw hr store read ws rs across j k same
  cases chosen : source block r k with
  | initial => exact False.elim (required chosen)
  | store location byteIndex => simp [localSource,chosen]

end PtxTorchLean.Poisson.PTX.CellGrid

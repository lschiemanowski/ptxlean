import PoissonPTX.CellWhole

namespace PtxTorchLean.Poisson.PTX.CellGrid

/-- Uniform cell code and explicit launch-provided contexts. Each block has a
separate local state, including its barrier and private shared-memory views. -/
structure Launch (count : Nat) where
  width : Nat
  bases : Fin count → Space → Word
  (cells source output : Word)
  context : Fin count → Fin 32 → Kernel.Context

def config (block : Fin count) : Concurrent.Config 32 := ⟨block.val,by decide⟩

abbrev State (count : Nat) := Fin count → CellWhole.State
abbrev Event (count : Nat) := Fin count × Concurrent.Event 32
abbrev Index (count : Nat) := Fin count × (Fin 32 × IndexSources.Access)

/-- One actual fetched cell instruction may run in any block. The grid adds
scheduling and block identity, not an assumed cell result. Source constraints
are separate, just as for the underlying candidate execution. -/
inductive Runs (launch : Launch count) :
    State count → List (Event count) → List (Index count) → State count → Prop where
  | nil : Runs launch s [] [] s
  | cons (step : CellWhole.Step (config block) (launch.bases block) (BitVec.ofNat 32 block.val)
        launch.width launch.cells launch.source launch.output (launch.context block) thread (s block) out)
      (rest : Runs launch (Function.update s block out.state) events indices final) :
      Runs launch s (out.events.map (block,·)++events) (out.indices.map (block,·)++indices) final

def forBlock (block : Fin count) (records : List (Fin count × α)) : List α :=
  records.filterMap fun (owner,value) => if owner=block then some value else none

@[simp] theorem forBlock_append (block : Fin count) (a b : List (Fin count × α)) :
    forBlock block (a++b)=forBlock block a++forBlock block b := by simp [forBlock]

@[simp] theorem forBlock_tag (block owner : Fin count) (records : List α) :
    forBlock block (records.map (owner,·))=if owner=block then records else [] := by
  by_cases same : owner=block <;> simp [forBlock,same,List.filterMap_map]

variable {count : Nat} {launch : Launch count} {start final : State count}
  {events : List (Event count)} {indices : List (Index count)}

/-- Projection preserves the actual fetched whole-cell execution, all barrier
records, every word access and every integer-index access. -/
theorem project (run : Runs launch start events indices final) (block : Fin count) :
    CellWhole.Runs (config block) (launch.bases block) (BitVec.ofNat 32 block.val)
      launch.width launch.cells launch.source launch.output (launch.context block)
      (start block) (forBlock block events) (forBlock block indices) (final block) := by
  induction run with
  | nil => exact .nil
  | @cons selected thread s out events indices final step rest ih =>
    by_cases same : selected=block
    · subst selected
      simp only [Function.update_self] at ih
      simpa using CellWhole.Runs.cons step ih
    · simpa [same,Function.update,Ne.symm same] using ih

/-- A global byte has one identity throughout the grid. A shared byte is
qualified by its owning block, even when numeric addresses coincide. -/
inductive ByteAddress (count : Nat) where
  | global (address : Nat)
  | shared (block : Fin count) (address : Nat)
  deriving DecidableEq, Repr

def byteAddress (block : Fin count) : Space → Nat → ByteAddress count
  | .global => .global
  | .shared => .shared block

@[simp] theorem global_common (one two : Fin count) (address : Nat) :
    byteAddress one .global address=byteAddress two .global address := rfl

theorem shared_private (one two : Fin count) (different : one≠two) (a b : Nat) :
    byteAddress one .shared a≠byteAddress two .shared b := by
  simp only [byteAddress,ne_eq,ByteAddress.shared.injEq,not_and]
  intro equal
  exact False.elim (different equal)

end PtxTorchLean.Poisson.PTX.CellGrid

import PoissonPTX.CellGrid

namespace PtxTorchLean.Poisson.PTX.CellGrid
variable {count : Nat} {launch : Launch count}

/-- Concatenate actual grid schedules, retaining every event in order. -/
theorem append {start middle final : State count}
    (first : Runs launch start a ai middle) (second : Runs launch middle b bi final) :
    Runs launch start (a++b) (ai++bi) final := by
  induction first with
  | nil => exact second
  | cons step rest ih => simpa [List.append_assoc] using Runs.cons step (ih second)

/-- Execute one block's supplied fetched run without changing any other block. -/
theorem lift_block {block : Fin count} {start final : CellWhole.State}
    (localRun : CellWhole.Runs (config block) (launch.bases block) (BitVec.ofNat 32 block.val)
      launch.width launch.cells launch.source launch.output (launch.context block) start events indices final)
    (state : State count) (same : state block=start) :
    Runs launch state (events.map (block,·)) (indices.map (block,·)) (Function.update state block final) := by
  induction localRun generalizing state with
  | nil => simpa [← same] using (Runs.nil (launch:=launch) (s:=state))
  | @cons thread start out events indices final step rest ih =>
    have first : CellWhole.Step (config block) (launch.bases block) (BitVec.ofNat 32 block.val)
        launch.width launch.cells launch.source launch.output (launch.context block) thread (state block) out := by
      rw [same]; exact step
    have later := ih (Function.update state block out.state) (by simp)
    simpa [List.map_append] using Runs.cons first later

/-- State after a prefix of block indices, used only to construct a schedule. -/
def prefixState (start final : State count) (cut : Nat) : State count :=
  fun block => if block.val<cut then final block else start block

theorem prefix_update (start final : State count) (n : Nat) (inside : n<count) :
    Function.update (prefixState start final n) ⟨n,inside⟩ (final ⟨n,inside⟩)=prefixState start final (n+1) := by
  funext block
  by_cases eq : block=⟨n,inside⟩
  · subst block; simp [prefixState]
  · have ne : block.val≠n := fun equal => eq (Fin.ext equal)
    simp only [Function.update_of_ne eq,prefixState]
    have iff : block.val<n ↔ block.val<n+1 := by omega
    simp only [iff]

/-- A finite prefix of supplied local runs has an actual grid schedule. Its
projected records are exactly the supplied records of the scheduled blocks. -/
theorem prefix_exists (start final : State count)
    (events : Fin count → List (Concurrent.Event 32)) (indices : Fin count → List (Fin 32 × IndexSources.Access))
    (localRuns : ∀ block, CellWhole.Runs (config block) (launch.bases block) (BitVec.ofNat 32 block.val)
      launch.width launch.cells launch.source launch.output (launch.context block)
      (start block) (events block) (indices block) (final block)) (n : Nat) (bound : n≤count) :
    ∃ words indexes, Runs launch start words indexes (prefixState start final n) ∧
      (∀ block, forBlock block words=if block.val<n then events block else []) ∧
      (∀ block, forBlock block indexes=if block.val<n then indices block else []) := by
  induction n with
  | zero =>
    have states : prefixState start final 0=start := by funext block; simp [prefixState]
    exact ⟨[],[],by rw [states]; exact .nil,by simp [forBlock],by simp [forBlock]⟩
  | succ n ih =>
    obtain ⟨words,indexes,first,wordEq,indexEq⟩ := ih (by omega)
    have inside : n<count := by omega
    let block : Fin count := ⟨n,inside⟩
    have later := lift_block (localRuns block) (prefixState start final n) (by simp [prefixState,block])
    have complete := append first later
    rw [prefix_update start final n inside] at complete
    refine ⟨words++(events block).map (block,·),indexes++(indices block).map (block,·),complete,?_,?_⟩
    · intro other
      rw [forBlock_append,forBlock_tag,wordEq]
      by_cases eq : block=other
      · subst other; simp [block]
      · have ne : other.val≠n := fun equal => eq (Fin.ext equal.symm)
        have iff : other.val<n ↔ other.val<n+1 := by omega
        simp [eq,iff]
    · intro other
      rw [forBlock_append,forBlock_tag,indexEq]
      by_cases eq : block=other
      · subst other; simp [block]
      · have ne : other.val≠n := fun equal => eq (Fin.ext equal.symm)
        have iff : other.val<n ↔ other.val<n+1 := by omega
        simp [eq,iff]

/-- Schedule all blocks. This is conditional only on the supplied local runs;
no grid run or desired output is assumed. -/
theorem serial_exists (start final : State count)
    (events : Fin count → List (Concurrent.Event 32)) (indices : Fin count → List (Fin 32 × IndexSources.Access))
    (localRuns : ∀ block, CellWhole.Runs (config block) (launch.bases block) (BitVec.ofNat 32 block.val)
      launch.width launch.cells launch.source launch.output (launch.context block)
      (start block) (events block) (indices block) (final block)) :
    ∃ words indexes, Runs launch start words indexes final ∧
      (∀ block, forBlock block words=events block) ∧
      (∀ block, forBlock block indexes=indices block) := by
  obtain ⟨words,indexes,run,wordEq,indexEq⟩ := prefix_exists start final events indices localRuns count (by omega)
  have states : prefixState start final count=final := by funext block; simp [prefixState,block.isLt]
  exact ⟨words,indexes,by simpa [states] using run,
    fun block => by simpa [block.isLt] using wordEq block,
    fun block => by simpa [block.isLt] using indexEq block⟩

end PtxTorchLean.Poisson.PTX.CellGrid

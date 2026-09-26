import PtxBinary32.GridDenseDataMachine
import PtxBinary32.GridDenseReadData
import PtxBinary32.DenseDataMachine

namespace Ptx.Scalar.Parallel.GridDense
open Ptx.Scalar.Parallel.Dense

def DataInvariant (s : Dense.Shape) (global : List Word) (state : Grid.State s.rows s.width) : Prop :=
  ∀ g, LocalData.DataInvariant s global g (Grid.view state g)

def Stores (s : Dense.Shape) (global : List Word) (events : List (Grid.Event s.rows s.width)) : Prop :=
  ∀ g t space occ effect, (g,.scalar t (some space) occ) ∈ events → occ.memory=some effect → effect.kind=.store →
    StoreData s global (thread s g t) occ.pc effect.value

def Reads (s : Dense.Shape) (global : List Word) (events : List (Grid.Event s.rows s.width)) : Prop :=
  ∀ g t space occ effect, (g,.scalar t (some space) occ) ∈ events → occ.memory=some effect → effect.kind=.load →
    ReadData s global (thread s g t) occ.pc effect.value

theorem step_data (s : Dense.Shape) (b : Bounds s) (global : List Word)
    {state final : Grid.State s.rows s.width} {events : List (Grid.Event s.rows s.width)}
    (step : Grid.Step (config s b) (Dense.Compact.program s) state events final)
    (inv : DataInvariant s global state) (aligned : ∀ g, Parallel.Aligned (Grid.view state g))
    (reads : Reads s global events) : DataInvariant s global final ∧ Stores s global events := by
  cases step with
  | issue g t candidate out step =>
    have localReads : LocalData.Reads s global g out.events := by
      intro u space occ effect member memory load
      exact reads g u space occ effect (List.mem_map.mpr ⟨_,member,rfl⟩) memory load
    obtain ⟨data,stores⟩ := LocalData.step_data s b global g step (inv g) (aligned g) localReads
    constructor
    · intro h
      by_cases same : h=g
      · subst h; simpa using data
      · rw [Grid.view_install_other _ _ _ _ same]
        exact inv h
    · intro h u space occ effect member memory kind
      obtain ⟨e,he,eq⟩ := List.mem_map.mp member
      obtain ⟨rfl,rfl⟩ := Prod.mk.inj eq
      exact stores u space occ effect he memory kind

theorem scalar_step_singleton {state final : Grid.State groups n} {events : List (Grid.Event groups n)}
    (step : Grid.Step cfg code state events final) (g : Fin groups) (t : Fin n) (space : Option Space) (occ : Scalar.Occurrence)
    (member : (g,.scalar t space occ) ∈ events) : events=[(g,.scalar t space occ)] := by
  cases step with
  | issue h u candidate out step =>
    obtain ⟨e,he,eq⟩ := List.mem_map.mp member
    obtain ⟨rfl,rfl⟩ := Prod.mk.inj eq
    simp [Grid.tag,Dense.scalar_step_singleton step he]

/-- Actual global operands and earlier actual private stores supply every load
used in the arithmetic induction for the combined grid execution. -/
theorem run_data (s : Dense.Shape) (b : Bounds s) (global : List Word)
    (seeds : Fin s.threads → Scalar.State) {events : List (Grid.Event s.rows s.width)} {final : Grid.State s.rows s.width}
    (run : Grid.Runs (config s b) (Dense.Compact.program s) (initial s global seeds) events final)
    (halted : ∀ g t, ((final.blocks g).lanes t).halted=true) (source co)
    (valid : Admitted s global seeds events source co) : DataInvariant s global final ∧ Stores s global events := by
  have aux (current : Grid.State s.rows s.width) (rest : List (Grid.Event s.rows s.width))
      (tail : Grid.Runs (config s b) (Dense.Compact.program s) current rest final) :
      ∀ before, events=before++rest →
      Grid.Runs (config s b) (Dense.Compact.program s) (initial s global seeds) before current →
      DataInvariant s global current → Stores s global before →
      DataInvariant s global final ∧ Stores s global events := by
    induction tail with
    | nil =>
      intro before split prefixRun inv past
      simpa [split] using And.intro inv past
    | @cons state added middle rest finish step tail ih =>
      intro before split prefixRun inv past
      have reads : Reads s global added := by
        intro g reader space occ effect member memory load
        have singleton := scalar_step_singleton step g reader (some space) occ member
        have atQ : events[before.length]?=some (g,.scalar reader (some space) occ) := by rw [split,singleton]; simp
        apply read_data s b global seeds run halted source co valid before.length g reader space occ effect atQ memory load
        intro p hp writer so stored atP sm sk
        have inBefore : before[p]?=some (g,.scalar writer (some .shared) so) := by simpa [split,List.getElem?_append,hp] using atP
        exact past g writer .shared so stored (List.mem_of_getElem? inBefore) sm sk
      have aligned := Grid.runs_aligned prefixRun (initial_aligned s global seeds)
      obtain ⟨nextInv,newStores⟩ := step_data s b global step inv aligned reads
      have allStores : Stores s global (before++added) := by
        intro g owner space occ effect member memory store
        rcases List.mem_append.mp member with old | new
        · exact past g owner space occ effect old memory store
        · exact newStores g owner space occ effect new memory store
      exact ih run halted (before++added) (by simpa [List.append_assoc] using split)
        (Grid.runs_append prefixRun (by simpa using Grid.Runs.cons step Grid.Runs.nil)) nextInv allStores
  exact aux _ _ run [] (by simp) .nil (fun g t => Dense.initial_data s global [] seeds (thread s g t))
    (by intro _ _ _ _ _ member; simp at member)

end Ptx.Scalar.Parallel.GridDense

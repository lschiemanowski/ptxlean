import PtxBinary32.GridAccessControl
import PtxBinary32.GridFlatten
import PtxBinary32.DenseLoadSites

/-! One row per actual CTA, common fetched dense program, unchanged arithmetic
order. The original globally indexed scratch offsets are private to each group;
full extents are allocated explicitly, including unused rows. No GPU capacity or
runtime argument-passing claim follows from this representation. -/
namespace Ptx.Scalar.Parallel.GridDense

structure Bounds (s : Dense.Shape) : Prop where
  arithmetic : Dense.ArithmeticBounds s
  width : s.width≤1024

def config (s : Dense.Shape) (b : Bounds s) : Grid.Config s.width :=
  ⟨⟨94,70⟩,Dense.width_positive s,b.width⟩

def thread (s : Dense.Shape) (g : Fin s.rows) (t : Fin s.width) : Fin s.threads := Grid.flatThread g t

def initial (s : Dense.Shape) (global : List Word) (seeds : Fin s.threads → Scalar.State) : Grid.State s.rows s.width :=
  ⟨global,fun g => ⟨fun t => ⟨Dense.controlSeed s seeds (thread s g t),false⟩,
    List.replicate s.sharedWords 0,Barrier.reset 0,none⟩⟩

theorem thread_coordinates (s : Dense.Shape) (g : Fin s.rows) (t : Fin s.width) :
    (thread s g t).val/s.width=g.val ∧ (thread s g t).val%s.width=t.val := by
  have div := congrArg Fin.val (Grid.product_div g t)
  have mod := congrArg Fin.val (Grid.product_mod g t)
  exact ⟨div,mod⟩

theorem thread_unique (s : Dense.Shape) (g h : Fin s.rows) (t u : Fin s.width)
    (same : thread s g t=thread s h u) : g=h ∧ t=u := by
  exact Prod.mk.inj (finProdFinEquiv.injective same)

theorem initial_aligned (s : Dense.Shape) (global : List Word) (seeds : Fin s.threads → Scalar.State) :
    ∀ g, Parallel.Aligned (Grid.view (initial s global seeds) g) := by
  intro g t ht; simp [initial,Grid.view,Barrier.reset] at ht

theorem initial_control (s : Dense.Shape) (global : List Word) (seeds : Fin s.threads → Scalar.State) :
    ∀ g, AddressControl.Invariant (Dense.program s) (fun t => Dense.controlSeed s seeds (thread s g t))
      (Grid.view (initial s global seeds) g) := fun _ _ => AddressControl.agree_refl _

theorem candidate_control (s : Dense.Shape) (b : Bounds s) (global : List Word)
    (seeds : Fin s.threads → Scalar.State) {events : List (Grid.Event s.rows s.width)} {final : Grid.State s.rows s.width}
    (run : Grid.Runs (config s b) (Dense.program s) (initial s global seeds) events final) :
    ∀ g, AddressControl.Invariant (Dense.program s) (fun t => Dense.controlSeed s seeds (thread s g t)) (Grid.view final g) :=
  Grid.runs_address_control run _ (Dense.program_address_compatible s) (initial_aligned s global seeds) (initial_control s global seeds)

end Ptx.Scalar.Parallel.GridDense

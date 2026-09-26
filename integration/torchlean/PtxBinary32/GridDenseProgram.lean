import PtxBinary32.GridAccessControl
import PtxBinary32.GridFlatten
import PtxBinary32.CompactDenseAddressControl

/-! One row per actual CTA with compact private scratch. Logical indices still
select global operands; local columns select shared words. No GPU capacity or
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
    List.replicate (Dense.Compact.sharedWords s) 0,Barrier.reset 0,none⟩⟩

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
    ∀ g, AddressControl.Invariant (Dense.Compact.program s) (fun t => Dense.controlSeed s seeds (thread s g t))
      (Grid.view (initial s global seeds) g) := fun _ _ => AddressControl.agree_refl _

theorem candidate_control (s : Dense.Shape) (b : Bounds s) (global : List Word)
    (seeds : Fin s.threads → Scalar.State) {events : List (Grid.Event s.rows s.width)} {final : Grid.State s.rows s.width}
    (run : Grid.Runs (config s b) (Dense.Compact.program s) (initial s global seeds) events final) :
    ∀ g, AddressControl.Invariant (Dense.Compact.program s) (fun t => Dense.controlSeed s seeds (thread s g t)) (Grid.view final g) :=
  Grid.runs_address_control run _ (Dense.Compact.program_address_compatible s) (initial_aligned s global seeds) (initial_control s global seeds)

end Ptx.Scalar.Parallel.GridDense

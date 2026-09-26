import PtxBinary32.GridDenseProgram
import PtxBinary32.DenseLocalSegments
import PtxBinary32.ParallelSegmentSweep

/-! Control facts for a single physical group running logical dense lanes.
They are recovered from actual fetched prefixes, independently of read values. -/
namespace Ptx.Scalar.Parallel.GridDense.Local
open Dense

def initial (s : Shape) (g : Fin s.rows) (global shared : List Word)
    (seeds : Fin s.threads → Scalar.State) : Parallel.State s.width :=
  ⟨fun t => ⟨controlSeed s seeds (thread s g t),false⟩,global,shared,Barrier.reset 0,none⟩

theorem candidate_control (s : Shape) (b : GridDense.Bounds s) (g : Fin s.rows)
    (global shared : List Word) (seeds : Fin s.threads → Scalar.State)
    {events : List (Parallel.Event s.width)} {final : Parallel.State s.width}
    (run : Parallel.ConcreteRuns ((config s b).group g) (program s) (initial s g global shared seeds) events final) :
    AddressControl.Invariant (program s) (fun t => controlSeed s seeds (thread s g t)) final :=
  AddressControl.runs_invariant run.toRuns (program_address_compatible s)
    (fun _ => AddressControl.agree_refl _) (by intro t ht; simp [initial,Barrier.reset] at ht)

theorem coordinates_at_entry (s : Shape) (b : ArithmeticBounds s) (seeds : Fin s.threads → Scalar.State)
    (t : Fin s.threads) (k : Nat) (hk : k≤s.depth) :
    ControlCoordinates s t (AddressControl.atPC (program s) (controlSeed s seeds t) (22+16*k)) := by
  have len : (products s ++ (List.range k).flatMap (Dense.round s)).length=22+16*k := by
    simp [List.length_flatMap,List.sum_replicate,Nat.mul_comm]
  have coords := rounds_control_coordinates s t (List.range k) _
    (products_control_coordinates s b t (controlSeed s seeds t) (by simp [controlSeed]))
  by_cases last : k=s.depth
  · subst k
    have shape : program s=(products s ++ (List.range s.depth).flatMap (Dense.round s)) ++ output s ++ [] := by simp [program]
    rw [shape,← len,show (products s ++ (List.range s.depth).flatMap (Dense.round s)).length=
      (products s ++ (List.range s.depth).flatMap (Dense.round s)).length+0 by omega,
      control_atPC_slice _ _ _ _ 0 (by omega)]
    simpa [AddressControl.evaluate_append,AddressControl.evaluate] using coords
  · rw [program_round_split s k (by omega),← len,
      show (products s ++ (List.range k).flatMap (Dense.round s)).length=
        (products s ++ (List.range k).flatMap (Dense.round s)).length+0 by omega,
      control_atPC_slice _ _ _ _ 0 (by omega)]
    simpa [AddressControl.evaluate_append,AddressControl.evaluate] using coords

theorem entry_regs (s : Shape) (b : GridDense.Bounds s) (g : Fin s.rows)
    (global shared : List Word) (seeds : Fin s.threads → Scalar.State)
    {events : List (Parallel.Event s.width)} {final : Parallel.State s.width}
    (run : Parallel.ConcreteRuns ((config s b).group g) (program s) (initial s g global shared seeds) events final)
    (t : Fin s.width) (k : Nat) (hk : k≤s.depth) (pc : (final.lanes t).scalar.pc=22+16*k) :
    ControlCoordinates s (thread s g t) (final.lanes t).scalar := by
  have control := candidate_control s b g global shared seeds run t
  have coords := coordinates_at_entry s b.arithmetic seeds (thread s g t) k hk
  have r0 := control.regs 0 (by simp [AddressControl.Visible])
  have r1 := control.regs 1 (by simp [AddressControl.Visible])
  have r2 := control.regs 2 (by simp [AddressControl.Visible])
  rw [pc] at r0 r1 r2
  exact ⟨r0.trans coords.1,r1.trans coords.2.1,r2.trans coords.2.2⟩

theorem initial_reg (s : Shape) (b : GridDense.Bounds s) (g : Fin s.rows)
    (global shared : List Word) (seeds : Fin s.threads → Scalar.State)
    {events : List (Parallel.Event s.width)} {final : Parallel.State s.width}
    (run : Parallel.ConcreteRuns ((config s b).group g) (program s) (initial s g global shared seeds) events final)
    (t : Fin s.width) (pc : (final.lanes t).scalar.pc=0) :
    (final.lanes t).scalar.regs 0=BitVec.ofNat 32 (thread s g t).val := by
  have control := (candidate_control s b g global shared seeds run t).regs 0 (by simp [AddressControl.Visible])
  simpa [pc,AddressControl.atPC,AddressControl.evaluate,controlSeed] using control
end Ptx.Scalar.Parallel.GridDense.Local

import PtxBinary32.SoftmaxMemory

/-! In-place writeback and memory-domain checks for the sequential reference stages. -/
namespace Ptx.Scalar.SoftmaxMemory.Checks

/-- Both operands are loaded before the output overwrites the numerator. The
denominator and unrelated tail word remain in the same concrete arena. -/
theorem in_place_normalization : NormalizeLaunch ⟨94,70⟩ 0 1 0
    [0x40000000,0x40800000,0xdeadbeef] [0x3f000000,0x40800000,0xdeadbeef] := by
  apply normalize_launch_realize ⟨94,70⟩ 0 1 0
    [0x40000000,0x40800000,0xdeadbeef] 0x3f000000
    (by norm_num [Scalar.Binary32.SupportedTarget])
    (by norm_num [ValidIndex]) (by norm_num [ValidIndex]) (by norm_num [ValidIndex])
  refine ⟨0x3e800000,?_,?_⟩
  · decide
  · unfold Ptx.Binary32.Results
    decide

/-- Copying a constant into an existing word is a real fetched store. -/
theorem restore_unit_weight : StoreLaunch ⟨94,70⟩ 1 0x3f800000
    [0x3f000000,0x40800000,0xdeadbeef] [0x3f000000,0x3f800000,0xdeadbeef] := by
  exact store_launch_exists ⟨94,70⟩ 1 0x3f800000 _
    (by norm_num [Scalar.Binary32.SupportedTarget]) (by norm_num [ValidIndex])

/-- An out-of-bounds destination cannot be hidden by List.set's behavior. -/
theorem out_of_bounds_rejected (target : Ptx.Target) (word : Word) (before after : List Word) :
    ¬ StoreLaunch target before.length word before after := by
  rintro ⟨valid,_⟩
  exact Nat.lt_irrefl _ valid.1

/-- An index whose byte conversion would wrap cannot enter the component. -/
theorem wrapping_index_rejected (memory : List Word) : ¬ ValidIndex memory (2^62) := by
  intro valid
  exact Nat.lt_irrefl _ valid.2

/-- Unsupported targets cannot acquire a run through the launch wrapper. -/
theorem unsupported_target (target : Ptx.Target) (a b dst : Nat) (before after : List Word)
    (unsupported : ¬ Scalar.Binary32.SupportedTarget target) :
    ¬ NormalizeLaunch target a b dst before after := by
  rintro ⟨_,_,_,_,_,_,_,supported,_⟩
  exact unsupported supported

end Ptx.Scalar.SoftmaxMemory.Checks

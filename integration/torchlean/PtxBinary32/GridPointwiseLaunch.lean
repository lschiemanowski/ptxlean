import PtxBinary32.GridPointwise

/-! Actual multi-group launches at an array interface. The total thread count is
not limited to 1024; each nonempty group is. Logical padding is separate. -/
namespace Ptx.Scalar.Parallel.GridPointwise

inductive Launch (op : Pointwise.Op) (l : Layout groups n) (before : List Word) : List Word → Prop
  | empty (zero : groups=0) : Launch op l before before
  | kernel (cfg : Grid.Config n) (target : cfg.target=⟨94,70⟩) (positive : 0<groups*n)
      (seeds : Fin (groups*n) → Scalar.State) {events : List (Grid.Event groups n)} {final : Grid.State groups n}
      (run : Grid.Runs cfg (Pointwise.program op) (initial l before seeds) events final)
      (halted : ∀ g t, ((final.blocks g).lanes t).halted=true)
      (admitted : Admitted op l before seeds cfg target positive run) : Launch op l before final.global

theorem launch_exists (op : Pointwise.Op) (l : Layout groups n) (before : List Word)
    (positive : 0<n) (resource : n≤1024) (size : l.prefixWords+groups*n≤before.length) :
    ∃ after, Launch op l before after := by
  by_cases zero : groups=0
  · exact ⟨before,.empty zero⟩
  · let cfg : Grid.Config n := ⟨⟨94,70⟩,positive,resource⟩
    let seeds : Fin (groups*n) → Scalar.State := fun _ => ⟨0,fun _ => 0,fun _ => 0,fun _ => false,[]⟩
    have total : 0<groups*n := Nat.mul_pos (by omega) positive
    obtain ⟨events,final,run,halted,admitted⟩ := admitted_exists op l before seeds cfg rfl total size
    exact ⟨final.global,.kernel cfg rfl total seeds run halted admitted⟩

theorem launch_correct (run : Launch op l before after) :
    (∀ t, ∃ value, after[l.output t]?=some value ∧ Pointwise.Result op before[l.left t]! before[l.right t]! value) ∧
    (∀ i, i<l.prefixWords → after[i]?=before[i]?) ∧ after.length=before.length := by
  cases run with
  | empty zero =>
    exact ⟨by intro t; have := t.isLt; simp [zero] at this,fun _ _ => rfl,rfl⟩
  | kernel cfg target positive seeds run halted admitted =>
    have result := completed _ _ _ _ cfg target positive run halted admitted
    exact ⟨result.1,result.2.1,result.2.2.1⟩

end Ptx.Scalar.Parallel.GridPointwise

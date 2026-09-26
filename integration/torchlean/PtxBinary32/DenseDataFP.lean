import PtxBinary32.DenseData

namespace Ptx.Scalar.Parallel.Dense
open Ptx.Binary32

theorem product_fp_data (s : Shape) (global : List Word) (t : Fin s.threads)
    (a next : Scalar.State) (occ : Scalar.Binary32.Occurrence) (site : a.pc=16) (data : Data s global t a)
    (ev : Scalar.Binary32.Eval ⟨.always,.mul,6,.reg 5,.reg 4⟩ a next occ) : Data s global t next := by
  cases ev with
  | skipped no => cases no
  | @executed value enabled result =>
    have prod : Node s global (t.val/s.width) 0 (t.val%s.width) value := by
      apply node_leaf
      simpa [Scalar.Operand32.eval,data.input (by omega) (by omega),data.weight (by omega) (by omega),site] using result
    rcases data with ⟨tid,col,pg,inp,wei,old,rg,left,right,red,og,root,bias,aff,sign,out⟩
    constructor <;> simp only [Scalar.update,site,↓reduceIte,Nat.reduceAdd] at * <;> intros
    all_goals first | omega | assumption | (apply col; omega) | (apply pg <;> omega)

theorem round_fp_data (s : Shape) (global : List Word) (t : Fin s.threads)
    (a next : Scalar.State) (occ : Scalar.Binary32.Occurrence) (k : Nat) (hk : k<s.depth)
    (site : a.pc=22+16*k+9) (data : Data s global t a)
    (ev : Scalar.Binary32.Eval ⟨.pred 0 true,.add,6,.reg 4,.reg 5⟩ a next occ) : Data s global t next := by
  have gate := data.roundGate k hk (by omega) (by omega)
  cases ev with
  | skipped no =>
    have inactive : ¬t.val%s.width<2^(s.depth-(k+1)) := by simpa [Scalar.Guard.eval,gate] using no
    rcases data with ⟨tid,col,pg,inp,wei,old,rg,left,right,red,og,root,bias,aff,sign,out⟩
    constructor <;> simp only [site,Nat.reduceAdd] at * <;> intros
    all_goals first | omega | assumption | (apply col; omega) | (apply rg <;> omega) | skip
    rename_i phase h lo hi active
    have eq : phase=k := by omega
    subst phase
    exact False.elim (inactive active)
  | @executed value enabled result =>
    have active : t.val%s.width<2^(s.depth-(k+1)) := by simpa [Scalar.Guard.eval,gate] using enabled
    have prod : Node s global (t.val/s.width) (k+1) (t.val%s.width) value :=
      node_fork s global _ k _ _ _ value (data.left k hk (by omega) (by omega) active)
        (data.right k hk site active) result
    rcases data with ⟨tid,col,pg,inp,wei,old,rg,left,right,red,og,root,bias,aff,sign,out⟩
    constructor <;> simp only [Scalar.update,site,↓reduceIte,Nat.reduceAdd] at * <;> intros
    all_goals first | omega | assumption | (apply col; omega) | (apply rg <;> omega) | skip
    rename_i j hj lo hi enabled
    have eq : j=k := by omega
    subst j
    exact prod

theorem output_fp_data (s : Shape) (global : List Word) (t : Fin s.threads)
    (a next : Scalar.State) (occ : Scalar.Binary32.Occurrence)
    (site : a.pc=22+16*s.depth+11) (data : Data s global t a)
    (ev : Scalar.Binary32.Eval ⟨.pred 0 true,.add,6,.reg 6,.reg 8⟩ a next occ) : Data s global t next := by
  have gate := data.outputGate (by omega) (by omega)
  cases ev with
  | skipped no =>
    have inactive : t.val%s.width≠0 := by simpa [Scalar.Guard.eval,gate] using no
    rcases data with ⟨tid,col,pg,inp,wei,old,rg,left,right,red,og,root,bias,aff,sign,out⟩
    constructor <;> simp only [site,Nat.reduceAdd] at * <;> intros
    all_goals first | omega | assumption | (apply col; omega) | (apply og <;> omega)
  | @executed value enabled result =>
    have active : t.val%s.width=0 := by simpa [Scalar.Guard.eval,gate] using enabled
    have affine : ∃ dot, Node s global (t.val/s.width) s.depth 0 dot ∧ Results .add dot global[s.biasBase+t.val/s.width]! value := by
      refine ⟨a.regs 6,data.root (by omega) (by omega) active,?_⟩
      simpa [Scalar.Operand32.eval,data.bias site active] using result
    rcases data with ⟨tid,col,pg,inp,wei,old,rg,left,right,red,og,root,bias,aff,sign,out⟩
    constructor <;> simp only [Scalar.update,site,↓reduceIte,Nat.reduceAdd] at * <;> intros
    all_goals first | omega | assumption | (apply col; omega) | (apply og <;> omega)

end Ptx.Scalar.Parallel.Dense

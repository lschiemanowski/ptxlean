import PoissonPTX.CellStoreValues
import PoissonQuadCorrespondence

namespace PtxTorchLean.Poisson.PTX.Concurrent.CellMiddle.Numeric
open Symbolic Checks

/-- Matrix views of actual words; each multiplication follows TorchLean's
increasing-index fold, with no reassociation of floating-point sums. -/
def grid (width : Nat) (bases : Space → Word) (memory : Space → Nat → Word)
    (space : Space) (offset : Nat) : Correspondence.Grid Float width := fun i j =>
  decode (memory space (bases space+BitVec.ofNat 64 (offset+(i.val*width+j.val)*8)).toNat)

theorem entry_eval (width : Nat) (sp : Space) (offset row col : Nat) :
    (entry width sp offset row col).eval bases memory=
      decode (memory sp (bases sp+BitVec.ofNat 64 (offset+(row*width+col)*8)).toNat) := by
  simp [entry,Number.eval,Bits.eval,address,Symbolic.eval_add]

theorem sum_fold (ks : List Nat) (a b : Nat → Number) (z : Number) :
    ((ks.foldl (fun z k => Number.fp .add z (.fp .mul (a k) (b k))) z).eval bases memory)=
      ks.foldl (fun z k => z+(a k).eval bases memory*(b k).eval bases memory) (z.eval bases memory) := by
  induction ks generalizing z with
  | nil => rfl
  | cons k ks ih => simp [List.foldl_cons,ih,Number.eval,FP.apply]

theorem sum_eval (width : Nat) (a b : Nat → Number) :
    (sum width a b).eval bases memory=
      Correspondence.contraction (fun k : Fin width => (a k.val).eval bases memory)
        (fun k => (b k.val).eval bases memory) := by
  rw [sum,sum_fold,Correspondence.contraction_eq_fold]
  have indices : (List.finRange width).map Fin.val=List.range width := by
    apply List.ext_getElem
    · simp
    · intro i hi hj; simp
  rw [← indices,List.foldl_map]
  have zero : (Number.bits (.literal 0)).eval bases memory=(0 : Float) := by
    change decode (0 : Word)=(0 : Float)
    rfl
  rw [zero]

/-- The six formulas use already-published planes as operands. Substitution of
these equations below gives the complete three-phase tensor calculation. -/
def formula (width : Nat) (bases : Space → Word) (memory : Space → Nat → Word) (plane : Nat) :
    Correspondence.Grid Float width :=
  let b := grid width bases memory .global 0
  let d := grid width bases memory .global (width*width*8+32)
  let w := grid width bases memory .global (2*(width*width*8+32))
  let s p := grid width bases memory .shared (p*width*width*8)
  match plane with
  | 1 => Correspondence.product b (s 0)
  | 2 => Correspondence.product d (s 0)
  | 3 => fun i j => Correspondence.product (s 1) (Correspondence.transposed d) i j*w i j
  | 4 => fun i j => Correspondence.product (s 2) (Correspondence.transposed b) i j*w i j
  | 5 => Correspondence.product (Correspondence.transposed b) (s 3)
  | _ => Correspondence.product (Correspondence.transposed d) (s 4)

theorem row_col (i j : Fin width) : (i.val*width+j.val)/width=i.val ∧ (i.val*width+j.val)%width=j.val := by
  have hj := j.isLt
  constructor
  · rw [Nat.mul_comm i.val width,Nat.mul_add_div (by omega : 0<width),Nat.div_eq_of_lt hj,Nat.add_zero]
  · simp only [Nat.add_mod,Nat.mul_mod_left,Nat.zero_add,Nat.mod_eq_of_lt hj]

theorem expected_eval (plane : Fin 7) (positive : plane≠0) (i j : Fin width) :
    (expected width plane.val (i.val*width+j.val)).eval bases memory=formula width bases memory plane.val i j := by
  obtain ⟨row,col⟩ := row_col i j
  fin_cases plane <;> try contradiction
  all_goals simp only [expected,row,col,formula]
  all_goals simp only [Number.eval,FP.apply,sum_eval,entry_eval]
  all_goals rfl

/-- The byte address of each coordinate in any of the seven shared planes. -/
theorem shared_word_address (launch : Launch width bases start) (plane : Fin 7) (i j : Fin width) :
    (bases .shared+BitVec.ofNat 64 (plane.val*width*width*8+(i.val*width+j.val)*8)).toNat=
      SharedPlane.address (bases .shared).toNat width plane.val (i.val*width+j.val) := by
  let lane : Fin (width*width) := ⟨i.val*width+j.val,Correspondence.row_major_bound i j⟩
  have offBound : plane.val*width*width*8+(i.val*width+j.val)*8<7*width*width*8 := by
    have hp := plane.isLt
    have hl := lane.isLt
    have hprod := Nat.mul_le_mul_right (width*width) (show plane.val+1≤7 by omega)
    dsimp [lane] at hl
    nlinarith
  have nowrap : (bases .shared).toNat+(plane.val*width*width*8+(i.val*width+j.val)*8)<2^64 := by
    have h := launch.fits; omega
  have offSmall : plane.val*width*width*8+(i.val*width+j.val)*8<2^64 := by omega
  have physical : (bases .shared+BitVec.ofNat 64 (plane.val*width*width*8+(i.val*width+j.val)*8)).toNat=
      SharedPlane.address (bases .shared).toNat width plane.val lane.val := by
    rw [BitVec.toNat_add,BitVec.toNat_ofNat,Nat.mod_eq_of_lt offSmall,Nat.mod_eq_of_lt nowrap]
    simp [SharedPlane.address,lane,Nat.add_mul]
  exact physical

/-- For a completed concrete run all six shared matrices satisfy their ordered
numerical equations, with every input load and producer store derived. -/
theorem plane_equations (launch : Launch width bases start) (lo : 2≤width) (hi : width≤5)
    (run : Runs cfg (program width) start events final)
    (done : ∀ thread, (final.lanes thread).pc=(program width).length)
    (compatible : Visibility.Compatible initial events source) (performed : Visibility.Performed events source)
    (plane : Fin 7) (positive : plane≠0) :
    grid width bases (view width bases initial events) .shared (plane.val*width*width*8)=
      formula width bases (view width bases initial events) plane.val := by
  funext i j
  let lane : Fin (width*width) := ⟨i.val*width+j.val,Correspondence.row_major_bound i j⟩
  have value := plane_expression launch lo hi run done compatible performed plane positive lane
  have physical := shared_word_address launch plane i j
  change decode (view width bases initial events .shared
    (bases .shared+BitVec.ofNat 64 (plane.val*width*width*8+(i.val*width+j.val)*8)).toNat)=_
  rw [physical,value]
  exact expected_eval plane positive i j

end PtxTorchLean.Poisson.PTX.Concurrent.CellMiddle.Numeric

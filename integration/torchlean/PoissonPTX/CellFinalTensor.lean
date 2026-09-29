import PoissonPTX.CellFinalKernel

namespace PtxTorchLean.Poisson.PTX.CellFinal
open Contraction Correspondence
open Concurrent.CellMiddle

def bases (s : State) (sp : Space) : Word := s.regs (baseRegister sp)
def words (s : State) (sp : Space) (address : Nat) : Word := read64 (s.memory sp) address

def grid (s : State) (width : Nat) (sp : Space) (offset : Nat) : Grid Float width :=
  Numeric.grid width (bases s) (words s) sp offset

theorem value_grid (s : State) (hi : width≤5) (m : Matrix) (offset k : Nat)
    (row col : Fin width) (off : m.offset=BitVec.ofNat 64 offset)
    (hr : ((m.row.operand k).eval s).toNat=row.val)
    (hc : ((m.column.operand k).eval s).toNat=col.val) :
    value s width k m=grid s width m.space offset row col := by
  have small : row.val*width+col.val<2^32 := by
    have h := row_major_bound row col
    have ww : width*width≤25 := by nlinarith
    omega
  have ix := index_exact s width k m hi (by rw [hr]; exact row.isLt) (by rw [hc]; exact col.isLt)
  rw [hr,hc] at ix
  simp only [value,Contraction.location,ix,Nat.mod_eq_of_lt small,off,grid,Numeric.grid,bases,words]
  rw [BitVec.ofNat_add,BitVec.add_assoc,BitVec.add_comm (BitVec.ofNat 64 offset)]

theorem fold_fin (s : State) (width : Nat) (a b : Matrix) :
    fold s width a b=(List.finRange width).foldl
      (fun z k => z+value s width k.val a*value s width k.val b) 0 := by
  have indices : (List.finRange width).map Fin.val=List.range width := by
    apply List.ext_getElem
    · simp
    · intro i hi hj; simp
  rw [fold,← indices,List.foldl_map]

theorem fold_product (s : State) (hi : width≤5) (plane offset : Nat) (i j : Fin width)
    (row : (s.regs 16).toNat=i.val) (col : (s.regs 17).toNat=j.val) :
    fold s width (left width plane) (right (BitVec.ofNat 64 offset))=
      product (grid s width .shared (plane*width*width*8)) (grid s width .global offset) i j := by
  rw [fold_fin,product,contraction_eq_fold]
  have lv (k : Fin width) : value s width k.val (left width plane)=grid s width .shared (plane*width*width*8) i k := by
    apply value_grid s hi _ _ _ i k rfl
    · exact row
    · change (BitVec.ofNat 64 k.val).toNat=k.val
      rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by have := k.isLt; omega)]
  have rv (k : Fin width) : value s width k.val (right (BitVec.ofNat 64 offset))=grid s width .global offset k j := by
    apply value_grid s hi _ _ _ k j rfl
    · change (BitVec.ofNat 64 k.val).toNat=k.val
      rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by have := k.isLt; omega)]
    · exact col
  simp only [lv,rv]

/-- The final body reads complete byte-backed matrices, with exactly the
TorchLean product and addition order. -/
theorem result_tensor (s : State) (hi : width≤5) (b d : Nat) (i j : Fin width)
    (row : (s.regs 16).toNat=i.val) (col : (s.regs 17).toNat=j.val) :
    result s width (BitVec.ofNat 64 b) (BitVec.ofNat 64 d)=
      Spec.get2 (plus
        (Spec.matMulSpec (matrix (grid s width .shared (5*width*width*8))) (matrix (grid s width .global d)))
        (Spec.matMulSpec (matrix (grid s width .shared (6*width*width*8))) (matrix (grid s width .global b)))) i j := by
  have x := fold_product s hi 5 d i j row col
  have y := fold_product s hi 6 b i j row col
  change _=entries _ i j
  rw [entries_summed,entries_product,entries_product,entries_matrix,entries_matrix,entries_matrix,entries_matrix]
  exact congrArg₂ (fun a b : Float => a+b) x y

end PtxTorchLean.Poisson.PTX.CellFinal

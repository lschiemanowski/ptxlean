import PoissonPTX.CellWordView

namespace PtxTorchLean.Poisson.PTX.Concurrent.CellMiddle.Geometry

/-- Split an aligned in-range offset into its plane and row-major lane index. -/
theorem split_offset (width offset : Nat) (lo : 2≤width) (hi : width≤5)
    (aligned : offset%8=0) (bound : offset<7*width*width*8) :
    ∃ (plane : Fin 7) (lane : Fin 32), lane.val<width*width ∧
      offset=(plane.val*width*width+lane.val)*8 ∧ offset/(width*width*8)=plane.val := by
  have pos : 0<width*width := Nat.mul_pos (by omega) (by omega)
  have small : width*width≤25 := by nlinarith
  let p := offset/8/(width*width)
  let t := offset/8%(width*width)
  have ht : t<width*width := Nat.mod_lt _ pos
  have hp : p<7 := by
    dsimp [p]
    rw [Nat.div_div_eq_div_mul]
    apply (Nat.div_lt_iff_lt_mul (by omega : 0<8*(width*width))).mpr
    nlinarith
  refine ⟨⟨p,hp⟩,⟨t,by omega⟩,ht,?_,?_⟩
  · have h := Nat.mod_add_div offset 8
    have hq := Nat.mod_add_div (offset/8) (width*width)
    dsimp [p,t]
    calc
      offset=(offset/8)*8 := by omega
      _=((offset/8)%(width*width)+(width*width)*((offset/8)/(width*width)))*8 := by rw [hq]
      _=(_*width*width+_)*8 := by ring
  · simp [p,Nat.div_div_eq_div_mul,Nat.mul_assoc,Nat.mul_comm]

theorem plane_zero (width lane base : Nat) (active : lane<width*width) :
    base≤SharedPlane.address base width 0 lane ∧
      SharedPlane.address base width 0 lane+8≤base+width*width*8 := by
  simp only [SharedPlane.address,Nat.zero_mul,Nat.zero_add]
  omega

theorem plane_positive (width lane base : Nat) (p : Fin 7) (positive : p≠0) :
    base+width*width*8≤SharedPlane.address base width p.val lane := by
  have hp : 1≤p.val := by have h : p.val≠0 := fun e => positive (Fin.ext e); omega
  have h := Nat.le_mul_of_pos_left (width*width) hp
  unfold SharedPlane.address
  nlinarith

end PtxTorchLean.Poisson.PTX.Concurrent.CellMiddle.Geometry

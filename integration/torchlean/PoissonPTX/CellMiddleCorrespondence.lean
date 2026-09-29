import PoissonPTX.CellTensor

/-! Completed-execution correspondence for all six output planes of the concrete
three middle phases, including both weight multiplications and all shared reads. -/
namespace PtxTorchLean.Poisson.PTX.Concurrent.CellMiddle.Numeric
open Symbolic Checks Correspondence

/-- The actual TorchLean intermediate tensors in the local Poisson operator. -/
def target (b d w u : Mat Float width width) (plane : Nat) : Mat Float width width :=
  let bu := Spec.matMulSpec b u
  let du := Spec.matMulSpec d u
  let dx := hadamard w (Spec.matMulSpec bu (transpose d))
  let dy := hadamard w (Spec.matMulSpec du (transpose b))
  match plane with
  | 1 => bu
  | 2 => du
  | 3 => dx
  | 4 => dy
  | 5 => Spec.matMulSpec (transpose b) dx
  | _ => Spec.matMulSpec (transpose d) dy

def initialTensor (width : Nat) (bases : Space → Word) (initial : Space → Memory)
    (space : Space) (offset : Nat) : Mat Float width width :=
  matrix (grid width bases (fun sp addr => read64 (initial sp) addr) space offset)

theorem global_grid (width : Nat) (bases : Space → Word) (initial : Space → Memory)
    (events : List (Event 32)) (offset : Nat) :
    grid width bases (view width bases initial events) .global offset=
      entries (initialTensor width bases initial .global offset) := by
  rw [initialTensor,entries_matrix]; rfl

theorem input_grid (launch : Launch width bases start) (_lo : 2≤width) (_hi : width≤5) :
    grid width bases (view width bases initial events) .shared 0=
      entries (initialTensor width bases initial .shared 0) := by
  rw [initialTensor,entries_matrix]
  funext i j
  have bound := Correspondence.row_major_bound i j
  have fit := launch.fits
  have off : (i.val*width+j.val)*8<width*width*8 := by omega
  have nowrap : (bases .shared).toNat+(i.val*width+j.val)*8<2^64 := by nlinarith
  have small : (i.val*width+j.val)*8<2^64 := by omega
  simp only [grid,Nat.zero_add,BitVec.toNat_add,BitVec.toNat_ofNat,Nat.mod_eq_of_lt small,Nat.mod_eq_of_lt nowrap]
  simp [view,WordView.memory,show (bases .shared).toNat+(i.val*width+j.val)*8<(bases .shared).toNat+width*width*8 by omega]

/-- Pure substitution of the six ordered equations, preserving the rounding
order. Only commuting the two operands of a single Float product is needed. -/
theorem compose (width : Nat) (bases : Space → Word) (memory : Space → Nat → Word)
    (equations : ∀ p : Fin 7, p≠0 → grid width bases memory .shared (p.val*width*width*8)=formula width bases memory p.val)
    (plane : Fin 7) (positive : plane≠0) :
    grid width bases memory .shared (plane.val*width*width*8)=
      entries (target (matrix (grid width bases memory .global 0))
        (matrix (grid width bases memory .global (width*width*8+32)))
        (matrix (grid width bases memory .global (2*(width*width*8+32))))
        (matrix (grid width bases memory .shared 0)) plane.val) := by
  have h1 := equations ⟨1,by decide⟩ (by decide)
  have h2 := equations ⟨2,by decide⟩ (by decide)
  have h3 := equations ⟨3,by decide⟩ (by decide)
  have h4 := equations ⟨4,by decide⟩ (by decide)
  have h5 := equations ⟨5,by decide⟩ (by decide)
  have h6 := equations ⟨6,by decide⟩ (by decide)
  simp only [formula,Nat.zero_mul,Nat.one_mul] at h1 h2 h3 h4 h5 h6
  have commute (x w : Grid Float width) : (fun i j => x i j*w i j)=Correspondence.weighted w x := by
    funext i j; exact Binary64.mul_comm _ _
  rw [commute,h1] at h3
  rw [commute,h2] at h4
  rw [h3] at h5
  rw [h4] at h6
  fin_cases plane <;> try contradiction
  all_goals simp only [target,entries_product,entries_transpose,entries_weighted,entries_matrix]
  · simpa using h1
  · simpa using h2
  · simpa using h3
  · simpa using h4
  · simpa using h5
  · simpa using h6

/-- Every completed permitted candidate of the middle slice produces the six
TorchLean intermediate matrices on the actual initial coefficient/input bytes.
There is no per-load, phase-answer, supplied scalar trace or store-coverage premise. -/
theorem completed_middle (launch : Launch width bases start) (lo : 2≤width) (hi : width≤5)
    (execution : Concurrent.Runs cfg (program width) start events final)
    (done : ∀ thread, (final.lanes thread).pc=(program width).length)
    (compatible : Visibility.Compatible initial events source) (performed : Visibility.Performed events source)
    (plane : Fin 7) (positive : plane≠0) :
    grid width bases (view width bases initial events) .shared (plane.val*width*width*8)=
      entries (target (initialTensor width bases initial .global 0)
        (initialTensor width bases initial .global (width*width*8+32))
        (initialTensor width bases initial .global (2*(width*width*8+32)))
        (initialTensor width bases initial .shared 0) plane.val) := by
  have result := compose width bases (view width bases initial events)
    (plane_equations launch lo hi execution done compatible performed) plane positive
  have global (offset : Nat) : matrix (grid width bases (view width bases initial events) .global offset)=
      initialTensor width bases initial .global offset := rfl
  have input : matrix (grid width bases (view width bases initial events) .shared 0)=
      initialTensor width bases initial .shared 0 := by
    rw [input_grid launch lo hi,initialTensor,entries_matrix]
  simpa only [global,input] using result

/-- Each requested coordinate has an actual shared-store event whose decoded
word equals the corresponding TorchLean intermediate tensor coordinate. -/
theorem completed_store (launch : Launch width bases start) (lo : 2≤width) (hi : width≤5)
    (execution : Concurrent.Runs cfg (program width) start events final)
    (done : ∀ thread, (final.lanes thread).pc=(program width).length)
    (compatible : Visibility.Compatible initial events source) (performed : Visibility.Performed events source)
    (plane : Fin 7) (positive : plane≠0) (i j : Fin width) :
    ∃ (index : Nat) (thread : Fin 32) (access : Access),
      thread.val=i.val*width+j.val ∧ events[index]?=some (.data thread access) ∧
      access.data.store=true ∧ access.space=.shared ∧
      access.data.address=SharedPlane.address (bases .shared).toNat width plane.val (i.val*width+j.val) ∧
      decode access.data.value=Spec.get2 (target
        (initialTensor width bases initial .global 0)
        (initialTensor width bases initial .global (width*width*8+32))
        (initialTensor width bases initial .global (2*(width*width*8+32)))
        (initialTensor width bases initial .shared 0) plane.val) i j := by
  obtain ⟨index,thread,access,lane,observed,pc,store,shared,address⟩ :=
    producer launch lo hi execution done plane positive ⟨i.val*width+j.val,Correspondence.row_major_bound i j⟩
  refine ⟨index,thread,access,lane,observed,store,shared,address,?_⟩
  have result := congrFun (congrFun (completed_middle launch lo hi execution done compatible performed plane positive) i) j
  have owner := Checks.unique width lo hi execution launch.reset launch.pcs launch.base_nat launch.lane_nat launch.fits observed store shared
  have outside := Geometry.plane_positive width (i.val*width+j.val) (bases .shared).toNat plane positive
  rw [← address] at outside
  have word := WordView.output (initial:=initial) observed store shared owner outside
  change view width bases initial events .shared access.data.address=access.data.value at word
  change decode (view width bases initial events .shared
    (bases .shared+BitVec.ofNat 64 (plane.val*width*width*8+(i.val*width+j.val)*8)).toNat)=_ at result
  rw [shared_word_address launch plane i j,← address,word] at result
  exact result

end PtxTorchLean.Poisson.PTX.Concurrent.CellMiddle.Numeric

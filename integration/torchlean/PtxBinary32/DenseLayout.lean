import PtxBinary32.Reduction

/-! The first dense forward layout: one CTA, contiguous row-major global slices,
and fresh full-width shared planes. Bounds and ownership are arithmetic facts;
connecting them to fetched addresses is a separate kernel proof. -/
namespace Ptx.Scalar.Parallel.Dense

structure Shape where
  rows : Nat
  columns : Nat
  depth : Nat
  padded : columns ≤ 2^depth

def Shape.width (s : Shape) : Nat := 2^s.depth
def Shape.threads (s : Shape) : Nat := s.rows*s.width
def Shape.weightBase (s : Shape) : Nat := s.columns
def Shape.biasBase (s : Shape) : Nat := s.columns+s.rows*s.columns
def Shape.outputBase (s : Shape) : Nat := s.biasBase+s.rows
def Shape.globalWords (s : Shape) : Nat := s.outputBase+s.rows
def Shape.sharedWords (s : Shape) : Nat := (s.depth+1)*s.threads

def Shape.thread (s : Shape) (row column : Nat) : Nat := row*s.width+column
def Shape.weight (s : Shape) (row column : Nat) : Nat := s.weightBase+row*s.columns+column
def Shape.scratch (s : Shape) (round row column : Nat) : Nat := round*s.threads+s.thread row column

theorem width_positive (s : Shape) : 0 < s.width := by exact Nat.two_pow_pos _

theorem thread_bound (s : Shape) (row column : Nat) (hr : row < s.rows) (hc : column < s.width) :
    s.thread row column < s.threads := by
  unfold Shape.thread Shape.threads
  calc row*s.width+column < row*s.width+s.width := Nat.add_lt_add_left hc _
       _ = (row+1)*s.width := by simp [Nat.add_mul]
       _ ≤ s.rows*s.width := Nat.mul_le_mul_right _ hr

theorem thread_injective (s : Shape) (r c r' c' : Nat) (hc : c < s.width) (hc' : c' < s.width)
    (h : s.thread r c = s.thread r' c') : r=r' ∧ c=c' := by
  have hd := congrArg (· / s.width) h
  have hm := congrArg (· % s.width) h
  simp [Shape.thread,Nat.add_div,Nat.div_eq_of_lt hc,Nat.div_eq_of_lt hc',Nat.mod_eq_of_lt hc,Nat.mod_eq_of_lt hc',Nat.not_le.mpr hc,Nat.not_le.mpr hc',width_positive] at hd
  simp [Shape.thread,Nat.add_mod,Nat.mod_eq_of_lt hc,Nat.mod_eq_of_lt hc'] at hm
  exact ⟨hd,hm⟩

theorem weight_bound (s : Shape) (row column : Nat) (hr : row < s.rows) (hc : column < s.columns) :
    s.weightBase ≤ s.weight row column ∧ s.weight row column < s.biasBase := by
  have mul := Nat.mul_le_mul_right s.columns hr
  simp only [Shape.weight,Shape.biasBase,Shape.weightBase]
  constructor
  · omega
  · have : row*s.columns+column < s.rows*s.columns := by
      calc row*s.columns+column < row*s.columns+s.columns := Nat.add_lt_add_left hc _
           _ = (row+1)*s.columns := by simp [Nat.add_mul]
           _ ≤ s.rows*s.columns := mul
    omega

theorem global_slices (s : Shape) (row column : Nat) (hr : row < s.rows) (hc : column < s.columns) :
    column < s.weightBase ∧
    s.weightBase ≤ s.weight row column ∧ s.weight row column < s.biasBase ∧
    s.biasBase+row < s.outputBase ∧
    s.outputBase ≤ s.outputBase+row ∧ s.outputBase+row < s.globalWords := by
  have hw := weight_bound s row column hr hc
  simp only [Shape.outputBase,Shape.globalWords]
  exact ⟨hc,hw.1,hw.2,by omega,by omega,by omega⟩

theorem scratch_bound (s : Shape) (round row column : Nat)
    (hp : round ≤ s.depth) (hr : row < s.rows) (hc : column < s.width) :
    s.scratch round row column < s.sharedWords := by
  have ht := thread_bound s row column hr hc
  unfold Shape.scratch Shape.sharedWords
  calc round*s.threads+s.thread row column < round*s.threads+s.threads := Nat.add_lt_add_left ht _
       _ = (round+1)*s.threads := by simp [Nat.add_mul]
       _ ≤ (s.depth+1)*s.threads := Nat.mul_le_mul_right _ (by omega)

/-- Distinct (round,row,column) owners cannot denote the same scratch word. -/
theorem scratch_injective (s : Shape) (p r c p' r' c' : Nat)
    (hr : r < s.rows) (hc : c < s.width) (hr' : r' < s.rows) (hc' : c' < s.width)
    (same : s.scratch p r c = s.scratch p' r' c') : p=p' ∧ r=r' ∧ c=c' := by
  have ht := thread_bound s r c hr hc
  have ht' := thread_bound s r' c' hr' hc'
  have positive : 0 < s.threads := by omega
  have hp := congrArg (· / s.threads) same
  have hm := congrArg (· % s.threads) same
  simp [Shape.scratch,Nat.add_div,Nat.div_eq_of_lt ht,Nat.div_eq_of_lt ht',Nat.mod_eq_of_lt ht,Nat.mod_eq_of_lt ht',Nat.not_le.mpr ht,Nat.not_le.mpr ht',positive] at hp
  simp [Shape.scratch,Nat.add_mod,Nat.mod_eq_of_lt ht,Nat.mod_eq_of_lt ht'] at hm
  exact ⟨hp,thread_injective s r c r' c' hc hc' hm⟩

/-- The next round reads adjacent pairs from the previous plane. -/
theorem children_bound (s : Shape) (round column : Nat) (hp : round < s.depth)
    (hc : column < 2^(s.depth-(round+1))) :
    2*column < 2^(s.depth-round) ∧ 2*column+1 < 2^(s.depth-round) := by
  have eq : s.depth-round = (s.depth-(round+1))+1 := by omega
  rw [eq,pow_succ]
  omega

end Ptx.Scalar.Parallel.Dense

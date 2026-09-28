import PtxBinary32.UnaryPointwiseContract

/-! One fetched instruction list shared by every lane of a unary pass. Launch
state supplies each lane's own pointer and a read-only common pointer. All
arithmetic results retain the existing relational instruction semantics. -/
namespace Ptx.Scalar.UnaryPointwise
abbrev Instr := SoftmaxMemory.Instr

def ownLoad : Instr := .scalar (.plain (.load 0 (.reg 0)))
def commonLoad : Instr := .scalar (.plain (.load 1 (.reg 1)))
def ownStore : Instr := .scalar (.plain (.store (.reg 0) (.reg 2)))
def exitInstr : Instr := .scalar (.plain .exit)

def arithmetic : Op → List Instr
  | .shifted => [.binary (ShiftedExp.negate 1 2),.binary (ShiftedExp.shift 0 2),
      .binary (ShiftedExp.convert 2),.exponential (ShiftedExp.exponential 2)]
  | .normalize => [.reciprocal (Normalize.reciprocal 1 2),.binary (Normalize.multiply 0 2)]

def body (op : Op) : List Instr := [ownLoad,commonLoad] ++ arithmetic op ++ [ownStore]
def program (op : Op) : List Instr := body op ++ [exitInstr]

def storePC : Op → Nat | .shifted => 6 | .normalize => 4
def exitPC (op : Op) : Nat := storePC op+1

@[simp] theorem body_length (op : Op) : (body op).length=exitPC op := by
  cases op <;> simp [body,arithmetic,exitPC,storePC]
@[simp] theorem program_length (op : Op) : (program op).length=exitPC op+1 := by simp [program]
@[simp] theorem fetch_own (op : Op) : (program op)[0]?=some ownLoad := by cases op <;> rfl
@[simp] theorem fetch_common (op : Op) : (program op)[1]?=some commonLoad := by cases op <;> rfl
@[simp] theorem fetch_store (op : Op) : (program op)[storePC op]?=some ownStore := by cases op <;> rfl
@[simp] theorem fetch_exit (op : Op) : (program op)[exitPC op]?=some exitInstr := by cases op <;> rfl

def ScalarAllowed (i : Scalar.Instr) : Prop :=
  i=.plain (.load 0 (.reg 0)) ∨ i=.plain (.load 1 (.reg 1)) ∨
  i=.plain (.store (.reg 0) (.reg 2)) ∨ i=.plain .exit

/-- Scalar memory/control sites have exactly these four instruction forms. -/
theorem scalar_sites (op : Op) (pc : Nat) (i : Scalar.Instr)
    (fetch : (program op)[pc]?=some (.scalar i)) :
    (pc=0 ∧ i=.plain (.load 0 (.reg 0))) ∨
    (pc=1 ∧ i=.plain (.load 1 (.reg 1))) ∨
    (pc=storePC op ∧ i=.plain (.store (.reg 0) (.reg 2))) ∨
    (pc=exitPC op ∧ i=.plain .exit) := by
  cases op <;> simp only [program,body,arithmetic,ownLoad,commonLoad,ownStore,exitInstr,
    List.cons_append,List.nil_append,storePC,exitPC] at fetch ⊢
  all_goals
    have inside : pc<8 := by
      obtain ⟨bound,_⟩ := List.getElem?_eq_some_iff.mp fetch
      simp at bound
      omega
    interval_cases pc <;> simp_all

theorem scalar_allowed (op : Op) (pc : Nat) (i : Scalar.Instr)
    (fetch : (program op)[pc]?=some (.scalar i)) : ScalarAllowed i := by
  rcases scalar_sites op pc i fetch with h|h|h|h <;> simp_all [ScalarAllowed]

end Ptx.Scalar.UnaryPointwise

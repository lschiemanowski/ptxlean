import PoissonPTX.ConcurrentAddress

/-! Proof-only symbolic registers. Word expressions retain exact bits; numeric
expressions retain decoded Float values so permitted NaN encodings stay free. -/
namespace PtxTorchLean.Poisson.PTX.Concurrent.Symbolic

inductive Bits where
  | literal (word : Word)
  | base (space : Space)
  | add (a b : Bits)
  | mul32 (a b : Bits)
  | add32 (a b : Bits)
  | wide (a : Bits)
  | load (space : Space) (address : Bits)
  deriving DecidableEq, Repr

def Bits.eval (bases : Space → Word) (memory : Space → Nat → Word) : Bits → Word
  | .literal w => w
  | .base sp => bases sp
  | .add a b => a.eval bases memory + b.eval bases memory
  | .mul32 a b => PTX.mul32 (a.eval bases memory) (b.eval bases memory)
  | .add32 a b => PTX.add32 (a.eval bases memory) (b.eval bases memory)
  | .wide a => BitVec.ofNat 64 ((a.eval bases memory).toNat % 2^32 * 8)
  | .load sp a => memory sp (a.eval bases memory).toNat

inductive Number where
  | bits (a : Bits)
  | fp (op : FP) (a b : Number)
  deriving DecidableEq, Repr

def Number.eval (bases : Space → Word) (memory : Space → Nat → Word) : Number → Float
  | .bits a => decode (a.eval bases memory)
  | .fp op a b => op.apply (a.eval bases memory) (b.eval bases memory)

inductive Value where
  | unknown
  | bits (a : Bits)
  | number (a : Number)
  deriving DecidableEq, Repr

abbrev Registers := Nat → Value

def Rel (bases : Space → Word) (memory : Space → Nat → Word) (v : Value) (w : Word) : Prop :=
  match v with
  | .unknown => True
  | .bits a => w=a.eval bases memory
  | .number a => decode w=a.eval bases memory

def Matches (bases : Space → Word) (memory : Space → Nat → Word) (regs : Registers) (s : PTX.State) : Prop :=
  ∀ r, Rel bases memory (regs r) (s.regs r)

/-- Constant folding is exact bit-vector arithmetic, not real-number algebra. -/
def add (a b : Bits) : Bits :=
  match a,b with
  | .literal a,.literal b => .literal (a+b)
  | a,.literal 0 => a
  | .add a (.literal b),.literal c => .add a (.literal (b+c))
  | a,b => .add a b

def mul32 (a b : Bits) : Bits :=
  match a,b with
  | .literal a,.literal b => .literal (PTX.mul32 a b)
  | a,b => .mul32 a b

def add32 (a b : Bits) : Bits :=
  match a,b with
  | .literal a,.literal b => .literal (PTX.add32 a b)
  | a,b => .add32 a b

def wide (a : Bits) : Bits :=
  match a with
  | .literal a => .literal (BitVec.ofNat 64 (a.toNat % 2^32 * 8))
  | a => .wide a

theorem eval_add (a b : Bits) : (add a b).eval bases memory=a.eval bases memory+b.eval bases memory := by
  unfold add; split <;> simp_all [Bits.eval,BitVec.add_assoc]
theorem eval_mul32 (a b : Bits) : (mul32 a b).eval bases memory=PTX.mul32 (a.eval bases memory) (b.eval bases memory) := by
  cases a <;> cases b <;> rfl
theorem eval_add32 (a b : Bits) : (add32 a b).eval bases memory=PTX.add32 (a.eval bases memory) (b.eval bases memory) := by
  cases a <;> cases b <;> rfl
theorem eval_wide (a : Bits) : (wide a).eval bases memory=BitVec.ofNat 64 ((a.eval bases memory).toNat % 2^32 * 8) := by
  cases a <;> rfl

def operand (regs : Registers) : Operand → Value
  | .reg r => regs r
  | .imm w => .bits (.literal w)
  | .offset r w => match regs r with
    | .bits a => .bits (add a (.literal w))
    | _ => .unknown

def number : Value → Option Number
  | .unknown => none
  | .bits a => some (.bits a)
  | .number a => some a

def binary (f : Bits → Bits → Bits) : Value → Value → Value
  | .bits a,.bits b => .bits (f a b)
  | _,_ => .unknown

def widening : Value → Value
  | .bits a => .bits (wide a)
  | _ => .unknown

def floating (op : FP) (a b : Value) : Value :=
  match number a,number b with
  | some a,some b => .number (.fp op a b)
  | _,_ => .unknown

def loaded (sp : Space) : Value → Value
  | .bits a => .bits (.load sp a)
  | _ => .unknown

def data (regs : Registers) : Op → Registers
  | .mov dst src => Function.update regs dst (operand regs src)
  | .mul32 dst a b => Function.update regs dst (binary mul32 (operand regs a) (operand regs b))
  | .add32 dst a b => Function.update regs dst (binary add32 (operand regs a) (operand regs b))
  | .add64 dst a b => Function.update regs dst (binary add (operand regs a) (operand regs b))
  | .wide8 dst a => Function.update regs dst (widening (operand regs a))
  | .load64 sp dst a => Function.update regs dst (loaded sp (operand regs a))
  | .store64 .. => regs
  | .fp op dst a b => Function.update regs dst (floating op (operand regs a) (operand regs b))

theorem operand_sound (matchRegs : Matches bases memory regs s) (a : Operand) :
    Rel bases memory (operand regs a) (a.eval s) := by
  cases a with
  | reg r => exact matchRegs r
  | imm w => rfl
  | offset r w =>
    have h := matchRegs r
    unfold operand
    cases he : regs r <;> simp_all [Rel,Operand.eval,eval_add,Bits.eval]

theorem number_sound (related : Rel bases memory v w) (he : number v=some a) :
    decode w=a.eval bases memory := by
  cases v with
  | unknown => simp [number] at he
  | bits e =>
    simp only [number,Option.some.injEq] at he
    subst a
    change decode w=decode (e.eval bases memory)
    rw [show w=e.eval bases memory from related]
  | number e =>
    simp only [number,Option.some.injEq] at he
    subst a; exact related

theorem binary_sound {g : Word → Word → Word} (relatedA : Rel bases memory va wa) (relatedB : Rel bases memory vb wb)
    (sound : ∀ a b, (f a b).eval bases memory=g (a.eval bases memory) (b.eval bases memory)) :
    Rel bases memory (binary f va vb) (g wa wb) := by
  cases va <;> cases vb <;> simp_all [binary,Rel]

theorem widening_sound (related : Rel bases memory v w) :
    Rel bases memory (widening v) (BitVec.ofNat 64 (w.toNat % 2^32 * 8)) := by
  cases v <;> simp_all [widening,Rel,eval_wide]

theorem floating_sound (relatedA : Rel bases memory va wa) (relatedB : Rel bases memory vb wb)
    (result : op.Result wa wb out) : Rel bases memory (floating op va vb) out := by
  unfold floating
  split
  · rename_i a b ha hb
    change decode out=op.apply _ _
    rw [← number_sound relatedA ha,← number_sound relatedB hb]
    exact result
  · trivial

theorem assign_sound (hregs : Matches bases memory regs s) (related : Rel bases memory v w) :
    Matches bases memory (Function.update regs r v) (assign s r w) := by
  intro q
  by_cases eq : q=r
  · subst q; simpa [assign] using related
  · simpa [assign,advance,Function.update,eq] using hregs q

theorem data_sound (execution : Data op s t access) (hregs : Matches bases memory regs s)
    (reads : ∀ a, access=some a → a.data.store=false → a.data.value=memory a.space a.data.address) :
    Matches bases memory (data regs op) t := by
  cases execution with
  | ordinary plain he =>
    cases he with
    | mov => exact assign_sound hregs (operand_sound hregs _)
    | mul32 => exact assign_sound hregs (binary_sound (operand_sound hregs _) (operand_sound hregs _) eval_mul32)
    | add32 => exact assign_sound hregs (binary_sound (operand_sound hregs _) (operand_sound hregs _) eval_add32)
    | add64 => exact assign_sound hregs (binary_sound (operand_sound hregs _) (operand_sound hregs _) eval_add)
    | wide8 => exact assign_sound hregs (widening_sound (operand_sound hregs _))
    | load64 => simp [ordinary] at plain
    | store64 => simp [ordinary] at plain
    | fp result => exact assign_sound hregs (floating_sound (operand_sound hregs _) (operand_sound hregs _) result)
  | @load sp dst addr s word valid =>
    apply assign_sound hregs
    have hw := reads _ rfl rfl
    have ha := operand_sound hregs addr
    change Rel bases memory (loaded sp (operand regs addr)) word
    cases hs : operand regs addr <;> simp_all [loaded,Rel,Bits.eval]
  | store => cases ‹Space› <;> exact hregs

end PtxTorchLean.Poisson.PTX.Concurrent.Symbolic

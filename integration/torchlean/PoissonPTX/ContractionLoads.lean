import PoissonPTX.MemoryBlocks

/-! Actual indexed operands for the unrolled cell contractions. Shared storage
is a supplied phase snapshot here; this does not discharge barrier visibility. -/
namespace PtxTorchLean.Poisson.PTX.Contraction

inductive Coord where
  | row | column | inner
  deriving DecidableEq, Repr

def Coord.operand (k : Nat) : Coord → Operand
  | .row => .reg 16
  | .column => .reg 17
  | .inner => .imm (BitVec.ofNat 64 k)

structure Matrix where
  space : Space
  offset : Word
  row : Coord
  column : Coord
  deriving DecidableEq, Repr

def indexWord (s : State) (width k : Nat) (m : Matrix) : Word :=
  add32 (mul32 ((m.row.operand k).eval s) (BitVec.ofNat 64 width))
    ((m.column.operand k).eval s)

def baseRegister : Space → Nat | .global => 0 | .shared => 3

def location (s : State) (width k : Nat) (m : Matrix) : Word :=
  s.regs (baseRegister m.space) +
    BitVec.ofNat 64 ((indexWord s width k m).toNat % 2^32 * 8) + m.offset

def value (s : State) (width k : Nat) (m : Matrix) : Float :=
  decode (read64 (s.memory m.space) (location s width k m).toNat)

def Valid (s : State) (width k : Nat) (m : Matrix) : Prop :=
  Valid64 (s.start m.space) (s.bytes m.space) (location s width k m).toNat

def indexCode (width k : Nat) (m : Matrix) : List Op :=
  [.mul32 13 (m.row.operand k) (.imm (BitVec.ofNat 64 width)),
   .add32 13 (.reg 13) (m.column.operand k)]

def loadCode (width k dst : Nat) (m : Matrix) : List Op :=
  indexCode width k m ++
  [.wide8 1 (.reg 13), .add64 2 (.reg (baseRegister m.space)) (.reg 1)] ++
  match m.space with
  | .global => [.add64 2 (.reg 2) (.imm m.offset), .load64 .global dst (.reg 2)]
  | .shared => [.load64 .shared dst (.offset 2 m.offset)]

def indexed (s : State) (width k : Nat) (m : Matrix) : State :=
  assign (assign s 13 (mul32 ((m.row.operand k).eval s) (BitVec.ofNat 64 width)))
    13 (indexWord s width k m)

def loaded (s : State) (width k dst : Nat) (m : Matrix) : State :=
  let ix := indexed s width k m
  let a := assign (assign ix 1 (BitVec.ofNat 64 ((indexWord s width k m).toNat % 2^32 * 8)))
    2 (s.regs (baseRegister m.space) + BitVec.ofNat 64 ((indexWord s width k m).toNat % 2^32 * 8))
  let a := match m.space with | .global => assign a 2 (location s width k m) | .shared => a
  assign a dst (read64 (s.memory m.space) (location s width k m).toNat)

/-- Memory, allocation bounds and live index/base registers, without scratch. -/
def environment (s : State) :=
  (s.global,s.shared,s.globalStart,s.globalBytes,s.sharedStart,s.sharedBytes,
    s.regs 0,s.regs 3,s.regs 16,s.regs 17)

def Stable (s t : State) : Prop := environment t = environment s

theorem stable_refl (s : State) : Stable s s := rfl

theorem stable_trans (a : Stable s t) (b : Stable t u) : Stable s u := b.trans a

theorem stable_assign (s : State) (r : Nat) (w : Word)
    (h0 : r≠0) (h3 : r≠3) (h16 : r≠16) (h17 : r≠17) : Stable s (assign s r w) := by
  simp [Stable,environment,assign,advance,Ne.symm h0,Ne.symm h3,Ne.symm h16,Ne.symm h17]

theorem stable_location (h : Stable s t) : location t width k m = location s width k m := by
  simp only [Stable,environment,Prod.mk.injEq] at h
  rcases h with ⟨hg,hs,hgs,hgb,hss,hsb,h0,h3,h16,h17⟩
  cases m with
  | mk sp off row col =>
    cases sp <;> cases row <;> cases col <;>
      simp_all [location,indexWord,Coord.operand,Operand.eval,baseRegister]

theorem stable_valid (h : Stable s t) : Valid t width k m ↔ Valid s width k m := by
  rw [Valid,stable_location h]
  simp only [Stable,environment,Prod.mk.injEq] at h
  rcases h with ⟨hg,hs,hgs,hgb,hss,hsb,h0,h3,h16,h17⟩
  cases hsp : m.space <;> simp_all [Valid,State.start,State.bytes]

theorem stable_value (h : Stable s t) : value t width k m = value s width k m := by
  unfold value
  rw [stable_location h]
  simp only [Stable,environment,Prod.mk.injEq] at h
  rcases h with ⟨hg,hs,hgs,hgb,hss,hsb,h0,h3,h16,h17⟩
  cases hsp : m.space <;> simp_all [State.memory]

theorem wide_byte_offset (v : Nat) : (v % 4294967296 * 8) % 18446744073709551616 = v % 4294967296 * 8 := by
  apply Nat.mod_eq_of_lt
  have h := Nat.mod_lt v (by decide : 0 < 2^32)
  omega

/-- Exact evaluation of the index, address calculation and checked byte load. -/
theorem load_run (s : State) (width k dst : Nat) (m : Matrix)
    (valid : Valid s width k m) :
    run (loadCode width k dst m) s = some (loaded s width k dst m) := by
  rcases m with ⟨sp,off,row,col⟩
  cases sp <;> cases row <;> cases col <;>
    simp_all [wide_byte_offset,Valid,loadCode,indexCode,run,eval,Operand.eval,Coord.operand,
      baseRegister,indexWord,location,loaded,indexed,assign,advance,State.memory,State.start,State.bytes]

theorem load_eq (execution : Block (loadCode width k dst m) s t)
    (valid : Valid s width k m) : t = loaded s width k dst m := by
  have hn : ∀ op ∈ loadCode width k dst m, noFP op = true := by
    cases hsp : m.space <;> simp [loadCode,indexCode,noFP,hsp]
  exact Option.some.inj ((block_complete execution hn).symm.trans (load_run s width k dst m valid))

theorem loaded_reg (s : State) (width k dst : Nat) (m : Matrix) :
    (loaded s width k dst m).regs dst = read64 (s.memory m.space) (location s width k m).toNat := by
  simp [loaded,assign]

theorem loaded_preserves (s : State) (width k dst r : Nat) (m : Matrix)
    (h1 : r≠1) (h2 : r≠2) (h13 : r≠13) (hd : r≠dst) :
    (loaded s width k dst m).regs r = s.regs r := by
  cases hsp : m.space <;> simp [loaded,indexed,assign,advance,h1,h2,h13,hd,hsp]

theorem loaded_stable (s : State) (width k dst : Nat) (m : Matrix)
    (h0 : dst≠0) (h3 : dst≠3) (h16 : dst≠16) (h17 : dst≠17) :
    Stable s (loaded s width k dst m) := by
  cases hsp : m.space <;>
    simp [Stable,environment,loaded,indexed,assign,advance,hsp,
      Ne.symm h0,Ne.symm h3,Ne.symm h16,Ne.symm h17]

end PtxTorchLean.Poisson.PTX.Contraction

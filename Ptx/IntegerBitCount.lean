import Ptx.ScalarText

/-! PTX 9.4 §§9.7.1.15–.16: `popc.b32` and `clz.b32` were introduced
in PTX 2.0 and require sm_20 or newer. Both accept every b32 value and write
a u32 result. Only these b32 spellings are modeled here; the ISA's b64 forms
and other widths/modifiers are not. The package's u32 result name is not a
mnemonic spelling. The separate memory eligibility mechanism does not check
these arithmetic forms.
-/
namespace Ptx.Scalar.IntegerBitCount

open Ptx.Scalar

theorem unary_exec (s : State) (operation : UnaryOp) (destination : Nat)
    (source : Operand32) (guard : Guard) (h : guard.eval s = true)
    (readOverride : Option Word) :
    eval readOverride ⟨guard, .unary32 operation destination source⟩ s =
      .next {({s with pc := s.pc + 1}) with
        regs := update s.regs destination (operation.eval (source.eval s))}
        (occurrence s ⟨guard, .unary32 operation destination source⟩ true) :=
  Ptx.Scalar.unary_exec s operation destination source guard h readOverride

theorem unary_false (s : State) (operation : UnaryOp) (destination : Nat)
    (source : Operand32) (guard : Guard) (h : guard.eval s = false)
    (readOverride : Option Word) :
    eval readOverride ⟨guard, .unary32 operation destination source⟩ s =
      .next {s with pc := s.pc + 1}
        (occurrence s ⟨guard, .unary32 operation destination source⟩ false) :=
  Ptx.Scalar.unary_false s operation destination source guard h readOverride

theorem unary_preserves_other (s : State) (operation : UnaryOp) (destination other : Nat)
    (source : Operand32) (guard : Guard) (h : guard.eval s = true)
    (different : other ≠ destination) (readOverride : Option Word) :
    (match eval readOverride ⟨guard, .unary32 operation destination source⟩ s with
      | .next next _ => next.regs other | _ => s.regs other) = s.regs other :=
  Ptx.Scalar.unary_preserves_other s operation destination other source guard h different readOverride

theorem takeWhile_length_le {α : Type} (p : α → Bool) : ∀ xs : List α,
    (xs.takeWhile p).length ≤ xs.length
  | [] => by simp
  | x :: xs => by
      cases hp : p x
      · simp [List.takeWhile, hp]
      · simp [List.takeWhile, hp, takeWhile_length_le p xs]

theorem takeWhile_length_eq_iff {α : Type} (p : α → Bool) : ∀ xs : List α,
    (xs.takeWhile p).length = xs.length ↔ ∀ x ∈ xs, p x = true
  | [] => by simp
  | x :: xs => by
      cases hp : p x
      · simp [List.takeWhile, hp]
      · simp [List.takeWhile, hp, takeWhile_length_eq_iff p xs]

theorem popc_toNat (a : Word) : (UnaryOp.eval .popc a).toNat =
    ((List.range 32).filter (fun i => a.getLsbD i)).length := by
  have : ((List.range 32).filter (fun i => a.getLsbD i)).length ≤ 32 :=
    by simpa using List.length_filter_le (fun i => a.getLsbD i) (List.range 32)
  have hlt : ((List.range 32).filter (fun i => a.getLsbD i)).length < 2^32 := by omega
  simp [UnaryOp.eval, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]

theorem clz_toNat (a : Word) : (UnaryOp.eval .clz a).toNat =
    ((List.range 32).reverse.takeWhile (fun i => !a.getLsbD i)).length := by
  have h : ((List.range 32).reverse.takeWhile (fun i => !a.getLsbD i)).length ≤ 32 := by
    simpa using takeWhile_length_le (fun i => !a.getLsbD i) (List.range 32).reverse
  have hlt : ((List.range 32).reverse.takeWhile (fun i => !a.getLsbD i)).length < 2^32 := by omega
  simp [UnaryOp.eval, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]

theorem popc_bound (a : Word) : (UnaryOp.eval .popc a).toNat ≤ 32 := by
  rw [popc_toNat]
  simpa using List.length_filter_le (fun i => a.getLsbD i) (List.range 32)

theorem clz_bound (a : Word) : (UnaryOp.eval .clz a).toNat ≤ 32 := by
  rw [clz_toNat]
  have h : ((List.range 32).reverse.takeWhile (fun i => !a.getLsbD i)).length ≤ 32 := by
    simpa using takeWhile_length_le (fun i => !a.getLsbD i) (List.range 32).reverse
  exact h

theorem popc_zero_iff (a : Word) : UnaryOp.eval .popc a = 0 ↔ a = 0 := by
  constructor
  · intro h
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    have hn := popc_toNat a
    rw [h] at hn
    have hn : ((List.range 32).filter (fun j => a.getLsbD j)).length = 0 := by simpa using hn.symm
    have hmem : i ∈ List.range 32 := List.mem_range.mpr hi
    have hfalse : a.getLsbD i = false := by
      cases hv : a.getLsbD i
      · rfl
      · have hm : i ∈ (List.range 32).filter (fun j => a.getLsbD j) :=
          List.mem_filter.mpr ⟨hmem, hv⟩
        have hne : (List.range 32).filter (fun j => a.getLsbD j) ≠ [] := by
          intro heq
          have : i ∈ ([] : List Nat) := heq ▸ hm
          simp at this
        have hpos : 0 < ((List.range 32).filter (fun j => a.getLsbD j)).length :=
          List.length_pos_iff.mpr hne
        omega
    simpa using hfalse
  · rintro rfl
    change BitVec.ofNat 32 ((List.range 32).filter (fun _ => false)).length = 0
    rfl

theorem clz_width_iff (a : Word) : UnaryOp.eval .clz a = 32 ↔ a = 0 := by
  rw [← BitVec.toNat_inj]
  rw [clz_toNat]
  constructor
  · intro h
    have hlen : ((List.range 32).reverse.takeWhile (fun i => !a.getLsbD i)).length = 32 := by
      simpa [BitVec.toNat_ofNat] using h
    have hall := (takeWhile_length_eq_iff (fun i => !a.getLsbD i)
      (List.range 32).reverse).mp (by simpa using hlen)
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    have himem : i ∈ (List.range 32).reverse := List.mem_reverse.mpr (List.mem_range.mpr hi)
    have hz := hall i himem
    cases hv : a.getLsbD i <;> simp_all
  · intro hz
    subst a
    have hall : ∀ i ∈ (List.range 32).reverse,
        Bool.not ((0#32).getLsbD i) = true := by
      intro i hi
      have hz : (0#32).getLsbD i = false := by simp
      simp [hz]
    have hlen := (takeWhile_length_eq_iff (fun i => Bool.not ((0#32).getLsbD i))
      (List.range 32).reverse).mpr hall
    simpa using hlen

/-! Kernel-reduced bit-pattern and interface examples. -/
example : UnaryOp.eval .popc 0 = 0 ∧ UnaryOp.eval .clz 0 = 32 := by decide
example : UnaryOp.eval .popc 2147483648 = 1 ∧ UnaryOp.eval .clz 2147483648 = 0 := by decide
example : UnaryOp.eval .popc 4294967295 = 32 ∧ UnaryOp.eval .clz 4294967295 = 0 := by decide
example : UnaryOp.eval .popc 1 = 1 ∧ UnaryOp.eval .clz 1 = 31 := by decide
example : UnaryOp.eval .popc 2147483653 = 3 ∧ UnaryOp.eval .clz 2147483653 = 0 := by decide

open Ptx.Scalar.Text

example : decodeOp "popc.b32" [.word (.reg 2), .word (.reg 2)] =
    .ok (.unary32 .popc 2 (.reg 2)) := rfl
example : decodeOp "clz.b32" [.word (.reg 0), .word (.imm 1)] =
    .ok (.unary32 .clz 0 (.imm 1)) := rfl
example : decodeOp "popc.b32" [.word (.reg 3), .word (.imm 4294967295)] =
    .ok (.unary32 .popc 3 (.imm 4294967295)) := rfl
example : decodeOp "clz.b32" [.word (.reg 4), .word (.reg 5)] =
    .ok (.unary32 .clz 4 (.reg 5)) := rfl
example : decodeOp "clz.b32" [.word (.imm 0), .word (.imm 1)] =
    .error (.invalidOperands "clz.b32") := rfl
example : decodeOp "popc.u32" [.word (.reg 0), .word (.imm 1)] =
    .error (.unsupportedMnemonic "popc.u32") := rfl
example : decodeOp "clz.b64" [.word (.reg 0), .word (.imm 1)] =
    .error (.unsupportedMnemonic "clz.b64") := rfl
example : supportedMnemonic "popc.b64" = false ∧ supportedMnemonic "clz.u32" = false := by decide

def sampleState : State :=
  ⟨7, fun i => if i = 0 then 2147483653 else 9,
    fun _ => 0, fun i => i = 0, []⟩

example : (eval none ⟨.always, .unary32 .popc 0 (.reg 0)⟩ sampleState) =
    .next {({sampleState with pc := 8}) with regs := update sampleState.regs 0 3}
      (occurrence sampleState ⟨.always, .unary32 .popc 0 (.reg 0)⟩ true) := by
  rw [unary_exec sampleState .popc 0 (.reg 0) .always (by rfl) none]
  rfl
example : (eval (some 4294967295) ⟨.always, .unary32 .clz 0 (.reg 0)⟩ sampleState) =
    .next {({sampleState with pc := 8}) with regs := update sampleState.regs 0 0}
      (occurrence sampleState ⟨.always, .unary32 .clz 0 (.reg 0)⟩ true) := by
  rw [unary_exec sampleState .clz 0 (.reg 0) .always (by rfl) (some 4294967295)]
  rfl

example : (eval none ⟨.pred 0 true, .unary32 .popc 1 (.reg 0)⟩ sampleState) =
    .next {({sampleState with pc := 8}) with regs := update sampleState.regs 1 3}
      (occurrence sampleState ⟨.pred 0 true, .unary32 .popc 1 (.reg 0)⟩ true) := by
  rw [unary_exec sampleState .popc 1 (.reg 0) (.pred 0 true) (by rfl) none]
  rfl
example : (eval none ⟨.pred 1 false, .unary32 .clz 1 (.imm 0)⟩ sampleState) =
    .next {({sampleState with pc := 8}) with regs := update sampleState.regs 1 32}
      (occurrence sampleState ⟨.pred 1 false, .unary32 .clz 1 (.imm 0)⟩ true) := by
  rw [unary_exec sampleState .clz 1 (.imm 0) (.pred 1 false) (by rfl) none]
  rfl
example : (eval none ⟨.pred 0 false, .unary32 .popc 1 (.imm 7)⟩ sampleState) =
    .next {sampleState with pc := 8}
      (occurrence sampleState ⟨.pred 0 false, .unary32 .popc 1 (.imm 7)⟩ false) := by
  rw [unary_false sampleState .popc 1 (.imm 7) (.pred 0 false) (by rfl) none]
  rfl
example : (eval none ⟨.pred 1 true, .unary32 .clz 1 (.reg 0)⟩ sampleState) =
    .next {sampleState with pc := 8}
      (occurrence sampleState ⟨.pred 1 true, .unary32 .clz 1 (.reg 0)⟩ false) := by
  rw [unary_false sampleState .clz 1 (.reg 0) (.pred 1 true) (by rfl) none]
  rfl
example : (occurrence sampleState ⟨.pred 0 true, .unary32 .popc 1 (.reg 0)⟩ false).reads =
    [.predicate 0] := rfl
example : (occurrence sampleState ⟨.always, .unary32 .clz 0 (.reg 0)⟩ true).memory = none := rfl
example : (occurrence sampleState ⟨.always, .unary32 .clz 0 (.reg 0)⟩ true).writes =
    [.word 0] := rfl

end Ptx.Scalar.IntegerBitCount

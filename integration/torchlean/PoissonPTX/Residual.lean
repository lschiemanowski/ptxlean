import PoissonPTX.MemoryBlocks

/-! The instruction body of true_residual: actual address calculations, byte
loads, rounded subtraction and byte store, for arbitrary input memory. -/
namespace PtxTorchLean.Poisson.PTX.Residual

/-- %a = 4, %b = 5, %c = 6, %global = 12. -/
def code (rhs ap output : Word) : List Op :=
  loadCode 4 12 rhs ++ loadCode 5 12 ap ++
    [.fp .sub 6 (.reg 4) (.reg 5)] ++ storeCode 6 12 output

def left (s : State) (rhs : Word) : State :=
  assign (addressed s 12 rhs) 4 (read64 s.global (address s 12 rhs).toNat)
def right (s : State) (rhs ap : Word) : State :=
  assign (addressed (left s rhs) 12 ap) 5 (read64 s.global (address s 12 ap).toNat)
def result (s : State) (rhs ap : Word) : Float :=
  decode (read64 s.global (address s 12 rhs).toNat) -
  decode (read64 s.global (address s 12 ap).toNat)
def finish (s : State) (rhs ap output value : Word) : State :=
  put (addressed (assign (right s rhs ap) 6 value) 12 output) .global
    (address s 12 output).toNat value

private theorem address_left (s : State) (rhs offset : Word) :
    address (left s rhs) 12 offset = address s 12 offset := by
  simp [address,wide,left,assign,advance,addressed]
private theorem address_right (s : State) (rhs ap offset : Word) :
    address (right s rhs ap) 12 offset = address s 12 offset := by
  simp [address,wide,right,left,assign,advance,addressed]
private theorem address_fp (s : State) (rhs ap value offset : Word) :
    address (assign (right s rhs ap) 6 value) 12 offset = address s 12 offset := by
  simp [address,wide,right,left,assign,advance,addressed]

/-- Existence comes from actual successful instruction steps, rather than from
an assumed implementation-output equation. -/
theorem executes (s : State) (rhs ap output : Word)
    (hr : Valid64 s.globalStart s.globalBytes (address s 12 rhs).toNat)
    (ha : Valid64 s.globalStart s.globalBytes (address s 12 ap).toNat)
    (ho : Valid64 s.globalStart s.globalBytes (address s 12 output).toNat) :
    Block (code rhs ap output) s (finish s rhs ap output (encode (result s rhs ap))) := by
  have lr := load_run s 4 12 rhs hr
  change run (loadCode 4 12 rhs) s = some (left s rhs) at lr
  have la := load_run (left s rhs) 5 12 ap (by simpa [left,assign,advance,addressed,address,wide] using ha)
  have la' : run (loadCode 5 12 ap) (left s rhs) = some (right s rhs ap) := by
    simpa [right,left,assign,advance,addressed,address,wide] using la
  have hs := store_run (assign (right s rhs ap) 6 (encode (result s rhs ap))) 6 12 output
    (by decide) (by decide) (by simpa [assign,advance,right,left,addressed,address,wide] using ho)
  have fp : Block [.fp .sub 6 (.reg 4) (.reg 5)] (right s rhs ap)
      (assign (right s rhs ap) 6 (encode (result s rhs ap))) := by
    apply Block.cons (Eval.fp ?_) Block.nil
    simp [FP.Result,FP.apply,Operand.eval,result,right,left,assign,advance,addressed,address,wide]
  have stored : Block (storeCode 6 12 output)
      (assign (right s rhs ap) 6 (encode (result s rhs ap)))
      (finish s rhs ap output (encode (result s rhs ap))) := by
    simpa [finish,assign,advance,right,left,addressed,address,wide] using run_sound hs
  exact block_append (block_append (block_append (run_sound lr) (run_sound la')) fp) stored

/-- Universal value guarantee, including every NaN payload permitted by the
arithmetic relation. No arithmetic result is assumed in the premises. -/
theorem correct (s t : State) (rhs ap output : Word)
    (hr : Valid64 s.globalStart s.globalBytes (address s 12 rhs).toNat)
    (ha : Valid64 s.globalStart s.globalBytes (address s 12 ap).toNat)
    (ho : Valid64 s.globalStart s.globalBytes (address s 12 output).toNat)
    (execution : Block (code rhs ap output) s t) :
    decode (read64 t.global (address s 12 output).toNat) = result s rhs ap ∧
    (∀ p, p < (address s 12 output).toNat ∨ (address s 12 output).toNat+8 ≤ p →
      t.global p = s.global p) ∧ t.shared = s.shared := by
  obtain ⟨s1,h1,hrest⟩ := block_split (loadCode 4 12 rhs)
    (loadCode 5 12 ap ++ [.fp .sub 6 (.reg 4) (.reg 5)] ++ storeCode 6 12 output)
    (by simpa [code,List.append_assoc] using execution)
  have h1eq : s1 = left s rhs := load_block_eq h1 hr
  subst s1
  obtain ⟨s2,h2,hrest⟩ := block_split (loadCode 5 12 ap)
    ([.fp .sub 6 (.reg 4) (.reg 5)] ++ storeCode 6 12 output)
    (by simpa [List.append_assoc] using hrest)
  have h2eq : s2 = right s rhs ap := by
    simpa [right,left,assign,advance,addressed,address,wide] using
      load_block_eq h2 (by simpa [left,assign,advance,addressed,address,wide] using ha)
  subst s2
  cases hrest with
  | cons fp tail =>
    cases fp with
    | @fp _ _ _ _ _ value allowed =>
      have ht := store_block_eq tail (by decide) (by decide)
        (by simpa [assign,advance,right,left,addressed,address,wide] using ho)
      subst t
      simp only [Operand.eval,FP.Result,FP.apply] at allowed
      have valueEq : decode value = result s rhs ap := by
        simpa [right,left,assign,advance,addressed,address,wide,result] using allowed
      constructor
      · simpa [put,assign,advance,right,left,addressed,address,wide] using valueEq
      constructor
      · intro p hp
        simpa [put,assign,advance,right,left,addressed,address,wide] using
          write64_outside s.global (address s 12 output).toNat value p hp
      · rfl

/-- Connect the body proof to instruction fetch at its actual location in a
larger straight-line instruction list. Surrounding branch/barrier code is not
silently included in this theorem. -/
theorem fetched (s : State) (rhs ap output : Word) (precode suffix : List Op)
    (pc : s.pc = precode.length)
    (hr : Valid64 s.globalStart s.globalBytes (address s 12 rhs).toNat)
    (ha : Valid64 s.globalStart s.globalBytes (address s 12 ap).toNat)
    (ho : Valid64 s.globalStart s.globalBytes (address s 12 output).toNat) :
    ∃ t, Runs (precode++code rhs ap output++suffix) s t ∧
      decode (read64 t.global (address s 12 output).toNat) = result s rhs ap := by
  have h := executes s rhs ap output hr ha ho
  exact ⟨_,block_fetched h precode suffix pc,(correct _ _ _ _ _ hr ha ho h).1⟩

end PtxTorchLean.Poisson.PTX.Residual

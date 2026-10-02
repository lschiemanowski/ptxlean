import PoissonPTX.Kernel
import PoissonPTX.Bytes32

namespace PtxTorchLean.Poisson.PTX.Indexed

/-- Adds the four-byte unsigned index operations needed by gather and CSR
traversal. Existing eight-byte and floating operations retain their old rules. -/
inductive Instr where
  | data (op : Op)
  | mad32 (dst a : Nat) (scale : BitVec 32) (b : Nat)
  | wide4 (dst src : Nat)
  | load32 (dst addr : Nat)
  deriving DecidableEq, Repr

def mad (s : State) (a : Nat) (scale : BitVec 32) (b : Nat) : Word :=
  (Kernel.u32 (s.regs a)*scale+Kernel.u32 (s.regs b)).setWidth 64

def wide (s : State) (src : Nat) : Word :=
  BitVec.ofNat 64 ((Kernel.u32 (s.regs src)).toNat*4)

inductive Eval : Instr → State → State → Prop where
  | data (h : PTX.Eval op s t) : Eval (.data op) s t
  | mad32 : Eval (.mad32 dst a scale b) s (assign s dst (mad s a scale b))
  | wide4 : Eval (.wide4 dst src) s (assign s dst (wide s src))
  | load32 (valid : Valid32 s.globalStart s.globalBytes (s.regs addr).toNat) :
      Eval (.load32 dst addr) s (assign s dst ((read32 s.global (s.regs addr).toNat).setWidth 64))

def eval : Instr → State → Option State
  | .data op,s => PTX.eval op s
  | .mad32 dst a scale b,s => some (assign s dst (mad s a scale b))
  | .wide4 dst src,s => some (assign s dst (wide s src))
  | .load32 dst addr,s => if Valid32 s.globalStart s.globalBytes (s.regs addr).toNat then
      some (assign s dst ((read32 s.global (s.regs addr).toNat).setWidth 64)) else none

def noFP : Instr → Bool
  | .data op => PTX.noFP op
  | _ => true

inductive Block : List Instr → State → State → Prop where
  | nil : Block [] s s
  | cons : Eval i s t → Block rest t u → Block (i::rest) s u

def Step (code : List Instr) (s t : State) : Prop :=
  ∃ i, code[s.pc]?=some i ∧ Eval i s t

inductive Runs (code : List Instr) : State → State → Prop where
  | nil : Runs code s s
  | cons : Step code s t → Runs code t u → Runs code s u

def run : List Instr → State → Option State
  | [],s => some s
  | i::rest,s => eval i s >>= run rest

theorem eval_sound (h : eval i s=some t) : Eval i s t := by
  cases i with
  | data op => exact .data (PTX.eval_sound h)
  | mad32 => cases h; exact .mad32
  | wide4 => cases h; exact .wide4
  | load32 => simp only [eval] at h; split at h <;> simp_all; subst t; exact .load32 (by assumption)

theorem eval_complete (h : Eval i s t) (plain : noFP i=true) : eval i s=some t := by
  cases h with
  | data he => exact PTX.eval_complete he plain
  | _ => simp_all [eval]

theorem eval_pc (h : Eval i s t) : t.pc=s.pc+1 := by
  cases h with
  | data he => exact PTX.eval_pc he
  | _ => rfl

theorem run_sound (h : run code s=some t) : Block code s t := by
  induction code generalizing s with
  | nil => simp [run] at h; subst t; exact .nil
  | cons i rest ih =>
    cases step : eval i s with
    | none => simp [run,step] at h
    | some mid => exact .cons (eval_sound step) (ih (by simpa [run,step] using h))

theorem run_complete (h : Block code s t) (plain : ∀ i∈code, noFP i=true) : run code s=some t := by
  induction h with
  | nil => rfl
  | cons he _ ih =>
    simp only [run,eval_complete he (plain _ (by simp))]
    exact ih (fun i member => plain i (by simp [member]))

theorem block_pc (h : Block code s t) : t.pc=s.pc+code.length := by
  induction h with
  | nil => simp
  | cons he _ ih => rw [ih,eval_pc he]; simp only [List.length_cons]; omega

theorem block_fetched (h : Block code s t) (pre suffix : List Instr) (pc : s.pc=pre.length) :
    Runs (pre++code++suffix) s t := by
  induction h generalizing pre with
  | nil => exact .nil
  | @cons i s mid rest t he hb ih =>
    apply Runs.cons ⟨i,by simp [pc],he⟩
    have next : mid.pc=(pre++[i]).length := by simp [eval_pc he,pc]
    simpa [List.append_assoc] using ih (pre++[i]) next

theorem runs_pc_le (h : Runs code s t) : s.pc≤t.pc := by
  induction h with
  | nil => exact Nat.le_refl _
  | cons step _ ih => obtain ⟨_,_,he⟩ := step; have := eval_pc he; omega

theorem runs_eq_of_pc (h : Runs code s t) (pc : s.pc=t.pc) : s=t := by
  cases h with
  | nil => rfl
  | cons step rest => obtain ⟨_,_,he⟩ := step; have := eval_pc he; have := runs_pc_le rest; omega

theorem fetched_block (pre code suffix : List Instr) (h : Runs (pre++code++suffix) s t)
    (pc : s.pc=pre.length) (done : t.pc=pre.length+code.length) : Block code s t := by
  induction code generalizing pre s with
  | nil => have eq := runs_eq_of_pc h (by simpa using pc.trans done.symm); subst t; exact .nil
  | cons i rest ih =>
    cases h with
    | nil => simp only [List.length_cons] at done; omega
    | cons step tail =>
      obtain ⟨actual,fetch,he⟩ := step
      have same : i=actual := by simpa [pc] using fetch
      subst actual
      apply Block.cons he
      apply ih (pre++[i]) (by simpa [List.append_assoc] using tail)
      · simp [eval_pc he,pc]
      · simp only [List.length_append,List.length_cons,List.length_nil] at done ⊢; omega

end PtxTorchLean.Poisson.PTX.Indexed

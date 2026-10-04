import PoissonPTX.ScalarExtras

namespace PtxTorchLean.Poisson.PTX.Scalar

def eval (ctx : Kernel.Context) (i : Instr) (s : Flow.State) : Option Flow.State :=
  match i with
  | .base op => Flow.eval ctx op s
  | .sqrt dst a => some {s with core:=assign s.core dst (encode (Float.sqrt (decode (a.eval s.core))))}
  | .max dst a b => some {s with core:=assign s.core dst (encode (maximum (a.eval s.core) (b.eval s.core)))}
  | .store32 address value =>
      if Valid32 s.core.globalStart s.core.globalBytes (address.eval s.core).toNat
      then some (put32 s (address.eval s.core).toNat (Kernel.u32 (value.eval s.core))) else none
  | .predFP p yes op dst a b =>
      if s.predicates p=yes then some {s with core:=assign s.core dst (encode (op.apply (decode (a.eval s.core)) (decode (b.eval s.core))))}
      else some (Flow.next s)
  | op => some (simple op s)

theorem eval_sound (h : eval ctx i s=some t) : Eval ctx i s t := by
  cases i with
  | base op => exact .base (Flow.eval_sound h)
  | sqrt dst a => cases h; exact .sqrt (decode_encode _)
  | max dst a b => cases h; exact .max (decode_encode _)
  | store32 address value =>
    simp only [eval] at h
    split at h
    · cases h; exact .store32 (by assumption)
    · simp at h
  | predFP p yes op dst a b =>
    simp only [eval] at h
    split at h
    · cases h; exact .predFP (by assumption) (decode_encode _)
    · cases h; exact .skipFP (by assumption)
  | _ => cases h; exact .simple rfl

def tick (ctx : Kernel.Context) (program : List Instr) (s : Flow.State) : Option Flow.State :=
  if s.halted then none else program[s.core.pc]? >>= fun i => eval ctx i s

def execute (ctx : Kernel.Context) (program : List Instr) : Nat → Flow.State → Option Flow.State
  | 0,s => if s.halted then some s else none
  | fuel+1,s => if s.halted then some s else tick ctx program s >>= execute ctx program fuel

theorem tick_sound (h : tick ctx program s=some t) : Step ctx program s t := by
  unfold tick at h
  split at h
  · simp at h
  · rename_i running
    change (program[s.core.pc]?.bind fun i => eval ctx i s)=some t at h
    simp only [Option.bind_eq_some_iff] at h
    obtain ⟨i,fetch,step⟩ := h
    exact ⟨by cases h : s.halted <;> simp_all, i,fetch,eval_sound step⟩

theorem execute_sound (h : execute ctx program fuel s=some t) : Runs ctx program s t ∧ t.halted=true := by
  induction fuel generalizing s with
  | zero =>
    simp only [execute] at h
    split at h
    · cases h; exact ⟨.nil,by assumption⟩
    · simp at h
  | succ fuel ih =>
    simp only [execute] at h
    split at h
    · cases h; exact ⟨.nil,by assumption⟩
    · change ((tick ctx program s).bind (execute ctx program fuel))=some t at h
      simp only [Option.bind_eq_some_iff] at h
      obtain ⟨mid,step,rest⟩ := h
      obtain ⟨run,done⟩ := ih rest
      exact ⟨.cons (tick_sound step) run,done⟩

theorem segment_pc (step : Eval ctx i s t) (plain : segment i=true) : t.core.pc=s.core.pc+1 := by
  cases step with
  | base actual => exact Flow.linear_pc actual (Flow.segment_linear plain)
  | simple ordinary =>
    cases i <;> simp_all [Scalar.ordinary,simple,assign,advance,Flow.next]
    split <;> rfl
  | _ => rfl

theorem segment_running (step : Eval ctx i s t) (plain : segment i=true) : t.halted=s.halted := by
  cases step with
  | base actual => exact Flow.segment_running actual plain
  | simple ordinary =>
    cases i <;> simp_all [Scalar.ordinary,simple,assign,advance,Flow.next]
    split <;> rfl
  | _ => rfl

theorem sequence_append (one : Sequence ctx left s t) (two : Sequence ctx right t u) :
    Sequence ctx (left++right) s u := by
  induction one with
  | nil => exact two
  | cons running step rest ih => exact .cons running step (ih two)

theorem sequence_split (left right : List Instr) (run : Sequence ctx (left++right) s t) :
    ∃ middle, Sequence ctx left s middle ∧ Sequence ctx right middle t := by
  induction left generalizing s with
  | nil => exact ⟨s,.nil,run⟩
  | cons i left ih =>
    cases run with
    | cons running step rest =>
      obtain ⟨middle,first,last⟩ := ih rest
      exact ⟨middle,.cons running step first,last⟩

theorem sequence_pc (run : Sequence ctx code s t) (plain : ∀ i∈code, segment i=true) :
    t.core.pc=s.core.pc+code.length := by
  induction run with
  | nil => simp
  | cons running step rest ih =>
    rw [ih (fun j member => plain j (by simp [member])),segment_pc step (plain _ (by simp))]
    simp [Nat.add_comm,Nat.add_left_comm]

theorem sequence_running (run : Sequence ctx code s t) (plain : ∀ i∈code, segment i=true) :
    t.halted=s.halted := by
  induction run with
  | nil => rfl
  | cons running step rest ih =>
    exact (ih (fun j member => plain j (by simp [member]))).trans (segment_running step (plain _ (by simp)))

theorem sequence_base (run : Flow.Sequence ctx code s t) : Sequence ctx (code.map Instr.base) s t := by
  induction run with
  | nil => exact .nil
  | cons running step rest ih => exact .cons running (.base step) ih

theorem sequence_base_block (run : Sequence ctx (code.map Instr.base) s t) : Flow.Sequence ctx code s t := by
  induction code generalizing s with
  | nil => cases run; exact .nil
  | cons i code ih =>
    cases run with
    | cons running step rest =>
      cases step with
      | base actual => exact .cons running actual (ih rest)
      | simple ordinary => simp [Scalar.ordinary] at ordinary

end PtxTorchLean.Poisson.PTX.Scalar

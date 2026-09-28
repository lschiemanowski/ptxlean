import PtxBinary32.ShiftedExpProgram
import PtxBinary32.NormalizeProgram

/-! Sequential memory stages for the reference softmax pipeline. Memory reads
use the current arena, with checked aligned addresses; arithmetic keeps every
result permitted by the existing instruction contracts. -/
namespace Ptx.Scalar.SoftmaxMemory

inductive Instr where
  | scalar (i : Scalar.Instr)
  | binary (i : Scalar.Binary32.Instr)
  | exponential (i : Scalar.Exponential.Instr)
  | reciprocal (i : Scalar.Reciprocal.Instr)

inductive Eval : Instr → Scalar.State → Scalar.State → Prop where
  | scalar {i s t e} (step : Scalar.eval none i s = .next t e) : Eval (.scalar i) s t
  | binary {i s t e} (step : Scalar.Binary32.Eval i s t e) : Eval (.binary i) s t
  | exponential {i s t e} (step : Scalar.Exponential.Eval i s t e) : Eval (.exponential i) s t
  | reciprocal {i s t e} (step : Scalar.Reciprocal.Eval i s t e) : Eval (.reciprocal i) s t

/-- A finite list of actual fetched instructions; each transition checks the
current PC against the complete program. No reference arithmetic is selected. -/
inductive Executes (program : List Instr) : List Instr → Scalar.State → Scalar.State → Prop where
  | nil (s) : Executes program [] s s
  | cons {i rest s middle t} (fetch : program[s.pc]? = some i)
      (step : Eval i s middle) (tail : Executes program rest middle t) :
      Executes program (i::rest) s t

def Run (target : Ptx.Target) (program : List Instr) (s t : Scalar.State) : Prop :=
  Scalar.Binary32.SupportedTarget target ∧ s.pc=0 ∧ Executes program program s t

/-- Select an actual emitted memory effect at any position of a fetched run.
The scalar constructor retains the exact occurrence returned by `eval none`. -/
inductive AccessAt (program : List Instr) : List Instr → Scalar.State → Scalar.State → Scalar.MemoryEffect → Prop where
  | here {i rest s middle t event effect}
      (fetch : program[s.pc]?=some (.scalar i))
      (step : Scalar.eval none i s=.next middle event) (emitted : event.memory=some effect)
      (tail : Executes program rest middle t) : AccessAt program (.scalar i::rest) s t effect
  | later {i rest s middle t effect} (fetch : program[s.pc]?=some i)
      (step : Eval i s middle) (tail : AccessAt program rest middle t effect) :
      AccessAt program (i::rest) s t effect

theorem eval_length {i s t} (step : Eval i s t) : t.memory.length=s.memory.length := by
  cases step with
  | scalar h => exact Scalar.eval_memory_length h
  | binary h => exact congrArg List.length (Scalar.Binary32.eval_frame _ _ _ _ h).2.1
  | exponential h => exact congrArg List.length (Scalar.Exponential.eval_frame _ _ _ _ h).2.1
  | reciprocal h => exact congrArg List.length (Scalar.Reciprocal.eval_frame _ _ _ _ h).2.1

theorem executes_length {program code s t} (run : Executes program code s t) :
    t.memory.length=s.memory.length := by
  induction run with
  | nil => rfl
  | cons _ step _ ih => exact ih.trans (eval_length step)

/-- Safety comes from each executed load/store's checked address; no caller
address-validity premise is used in this theorem. -/
theorem access_safe {program code s t effect} (access : AccessAt program code s t effect) :
    Scalar.ValidAddress s.memory effect.address := by
  induction access with
  | here _ step emitted _ => exact Scalar.eval_memory_safe step emitted
  | later _ step _ ih => simpa only [Scalar.ValidAddress,eval_length step] using ih

/-- Every actual memory effect fits wholly inside the initial arena, and the
complete fetched instruction sequence preserves the allocation's length. -/
theorem run_memory_safe {target program s t} (run : Run target program s t) :
    t.memory.length=s.memory.length ∧ ∀effect, AccessAt program program s t effect →
      effect.address.toNat % 4=0 ∧ effect.address.toNat+4≤4*s.memory.length := by
  exact ⟨executes_length run.2.2,fun _ access => Scalar.validAddress_bytes (access_safe access)⟩

def address (index : Nat) : Address := BitVec.ofNat 64 (4*index)
def load (destination index : Nat) : Instr := .scalar (.plain (.load destination (.imm (address index))))
def store (index source : Nat) : Instr := .scalar (.plain (.store (.imm (address index)) (.reg source)))
def write (s : Scalar.State) (r : Nat) (value : Word) : Scalar.State :=
  {s with pc:=s.pc+1,regs:=Scalar.update s.regs r value}
def save (s : Scalar.State) (index : Nat) : Scalar.State :=
  {s with pc:=s.pc+1,memory:=s.memory.set index (s.regs 2)}

/-- Extent and no-wrap requirements for one word address. -/
def ValidIndex (memory : List Word) (index : Nat) : Prop := index<memory.length ∧ index<2^62

theorem address_index (memory : List Word) (index : Nat) (valid : ValidIndex memory index) :
    Scalar.addressIndex memory (address index)=.ok index := by
  have small : 4*index<2^64 := by have := valid.2; omega
  have addr : (address index).toNat=4*index := Nat.mod_eq_of_lt small
  simp [Scalar.addressIndex,addr,valid.1]

/-- The immediate pointer is aligned and lies inside the original arena. -/
theorem valid_address (memory : List Word) (index : Nat) (valid : ValidIndex memory index) :
    Scalar.ValidAddress memory (address index) :=
  (Scalar.addressIndex_ok_iff.mp (address_index memory index valid)).1

theorem load_iff (s t : Scalar.State) (r index : Nat) (valid : ValidIndex s.memory index) :
    Eval (load r index) s t ↔ t=write s r s.memory[index]! := by
  constructor
  · intro h; cases h with
    | scalar step =>
      simp [Scalar.eval,Scalar.Instr.plain,Scalar.Guard.eval,Scalar.Operand64.eval,
        address_index _ _ valid] at step
      simpa [write,List.getElem!_eq_getElem?_getD] using step.1.symm
  · rintro rfl
    apply Eval.scalar (e := Scalar.occurrence s (.plain (.load r (.imm (address index)))) true
      (some ⟨.load,address index,s.memory[index]!⟩))
    simp [Scalar.eval,Scalar.Instr.plain,Scalar.Guard.eval,Scalar.Operand64.eval,
      address_index _ _ valid,write]

theorem store_iff (s t : Scalar.State) (index : Nat) (valid : ValidIndex s.memory index) :
    Eval (store index 2) s t ↔ t=save s index := by
  constructor
  · intro h; cases h with
    | scalar step =>
      simp [Scalar.eval,Scalar.Instr.plain,Scalar.Guard.eval,Scalar.Operand64.eval,
        Scalar.Operand32.eval,address_index _ _ valid] at step
      exact step.1.symm
  · rintro rfl
    apply Eval.scalar (e := Scalar.occurrence s (.plain (.store (.imm (address index)) (.reg 2))) true
      (some ⟨.store,address index,s.regs 2⟩))
    simp [Scalar.eval,Scalar.Instr.plain,Scalar.Guard.eval,Scalar.Operand64.eval,
      Scalar.Operand32.eval,address_index _ _ valid,save]

theorem store_result {s t : Scalar.State} {index : Nat} (h : Eval (store index 2) s t)
    (valid : ValidIndex s.memory index) : t=save s index := (store_iff s t index valid).mp h

def shiftedProgram (input maximum output : Nat) : List Instr :=
  [load 0 input,load 1 maximum,
   .binary (ShiftedExp.negate 1 2),.binary (ShiftedExp.shift 0 2),
   .binary (ShiftedExp.convert 2),.exponential (ShiftedExp.exponential 2),store output 2]

def normalizeProgram (numerator denominator output : Nat) : List Instr :=
  [load 0 numerator,load 1 denominator,.reciprocal (Normalize.reciprocal 1 2),
   .binary (Normalize.multiply 0 2),store output 2]

/-- All intermediate words remain explicit, including the permitted exponential result. -/
def ShiftedStages (input maximum output : Word) : Prop :=
  ∃ negative shifted product,
    Ptx.Binary32.Results .mul maximum 0xbf800000 negative ∧
    Ptx.Binary32.Results .add input negative shifted ∧
    Ptx.Binary32.Results .mul shifted Ptx.Binary32.ExpArgument.constantWord product ∧
    Ptx.Binary32.Exponential.Results product output

def NormalizeStages (numerator denominator output : Word) : Prop :=
  ∃ inverse, Ptx.Binary32.Reciprocal.Results denominator inverse ∧
    Ptx.Binary32.Results .mul numerator inverse output

theorem executes_cons {p i rest s t} : Executes p (i::rest) s t ↔
    ∃ middle, p[s.pc]?=some i ∧ Eval i s middle ∧ Executes p rest middle t := by
  constructor
  · intro h; cases h with | cons fetch step tail => exact ⟨_,fetch,step,tail⟩
  · rintro ⟨_,fetch,step,tail⟩; exact .cons fetch step tail

theorem executes_nil {p s t} : Executes p [] s t ↔ t=s := by
  constructor
  · intro h; cases h; rfl
  · rintro rfl; exact .nil _

theorem binary_iff (i : Scalar.Binary32.Instr) (s t : Scalar.State)
    (enabled : i.guard=.always) : Eval (.binary i) s t ↔ ∃ value,
      Ptx.Binary32.Results i.operation (i.left.eval s) (i.right.eval s) value ∧
      t=write s i.destination value := by
  constructor
  · intro h; cases h with
    | binary step =>
      obtain ⟨value,hr,ht,_⟩ := (Scalar.Binary32.eval_true_iff _ _ _ _ (by simp [enabled,Guard.eval])).mp step
      exact ⟨value,hr,ht⟩
  · rintro ⟨value,hr,rfl⟩; exact .binary (.executed (by simp [enabled,Guard.eval]) hr)

theorem exponential_iff (i : Scalar.Exponential.Instr) (s t : Scalar.State)
    (enabled : i.guard=.always) : Eval (.exponential i) s t ↔ ∃ value,
      Ptx.Binary32.Exponential.Results (i.source.eval s) value ∧ t=write s i.destination value := by
  constructor
  · intro h; cases h with
    | exponential step =>
      obtain ⟨value,hr,ht,_⟩ := (Scalar.Exponential.eval_true_iff _ _ _ _ (by simp [enabled,Guard.eval])).mp step
      exact ⟨value,hr,ht⟩
  · rintro ⟨value,hr,rfl⟩; exact .exponential (.executed (by simp [enabled,Guard.eval]) hr)

theorem reciprocal_iff (i : Scalar.Reciprocal.Instr) (s t : Scalar.State)
    (enabled : i.guard=.always) : Eval (.reciprocal i) s t ↔ ∃ value,
      Ptx.Binary32.Reciprocal.Results (i.source.eval s) value ∧ t=write s i.destination value := by
  constructor
  · intro h; cases h with
    | reciprocal step =>
      obtain ⟨value,hr,ht,_⟩ := (Scalar.Reciprocal.eval_true_iff _ _ _ _ (by simp [enabled,Guard.eval])).mp step
      exact ⟨value,hr,ht⟩
  · rintro ⟨value,hr,rfl⟩; exact .reciprocal (.executed (by simp [enabled,Guard.eval]) hr)

/-- Frame shared by both stages: only r0/r1/r2 and one memory word change. -/
def Frame (s t : Scalar.State) (count index : Nat) (out : Word) : Prop :=
  t.pc=count ∧ t.memory=s.memory.set index out ∧ t.memory.length=s.memory.length ∧
  t.addrs=s.addrs ∧ t.preds=s.preds ∧ (∀r, r≠0 → r≠1 → r≠2 → t.regs r=s.regs r)

theorem normalize_correct (target : Ptx.Target) (s t : Scalar.State) (a b dst : Nat)
    (va : ValidIndex s.memory a) (vb : ValidIndex s.memory b) (vd : ValidIndex s.memory dst)
    (run : Run target (normalizeProgram a b dst) s t) :
    ∃out, NormalizeStages s.memory[a]! s.memory[b]! out ∧ Frame s t 5 dst out := by
  rcases run with ⟨_,start,trace⟩
  simp only [normalizeProgram,executes_cons,executes_nil] at trace
  rcases trace with ⟨s₁,_,l₀,s₂,_,l₁,s₃,_,r₀,s₄,_,r₁,s₅,_,st,last⟩
  have e₁ := (load_iff s s₁ 0 a va).mp l₀; subst s₁
  have e₂ := (load_iff (write s 0 s.memory[a]!) s₂ 1 b vb).mp l₁; subst s₂
  obtain ⟨inv,h₀,e₃⟩ := (reciprocal_iff _ _ _ rfl).mp r₀; subst s₃
  obtain ⟨out,h₁,e₄⟩ := (binary_iff _ _ _ rfl).mp r₁; subst s₄
  have e₅ := store_result st vd; subst s₅
  subst t
  refine ⟨out,⟨inv,?_,?_⟩,?_⟩
  · simpa [write,Normalize.reciprocal,Operand32.eval,Scalar.update] using h₀
  · simpa [write,Normalize.reciprocal,Normalize.multiply,Operand32.eval,Scalar.update] using h₁
  · simp only [Frame,save,write,Normalize.reciprocal,Normalize.multiply,Scalar.update,start]
    simp only [List.length_set,true_and,ite_true]
    intro r h0 h1 h2
    simp [h0,h1,h2]

theorem shifted_correct (target : Ptx.Target) (s t : Scalar.State) (a b dst : Nat)
    (va : ValidIndex s.memory a) (vb : ValidIndex s.memory b) (vd : ValidIndex s.memory dst)
    (run : Run target (shiftedProgram a b dst) s t) :
    ∃out, ShiftedStages s.memory[a]! s.memory[b]! out ∧ Frame s t 7 dst out := by
  rcases run with ⟨_,start,trace⟩
  simp only [shiftedProgram,executes_cons,executes_nil] at trace
  rcases trace with ⟨s₁,_,l₀,s₂,_,l₁,s₃,_,r₀,s₄,_,r₁,s₅,_,r₂,s₆,_,r₃,s₇,_,st,last⟩
  have e₁ := (load_iff s s₁ 0 a va).mp l₀; subst s₁
  have e₂ := (load_iff (write s 0 s.memory[a]!) s₂ 1 b vb).mp l₁; subst s₂
  obtain ⟨negative,h₀,e₃⟩ := (binary_iff _ _ _ rfl).mp r₀; subst s₃
  obtain ⟨shifted,h₁,e₄⟩ := (binary_iff _ _ _ rfl).mp r₁; subst s₄
  obtain ⟨product,h₂,e₅⟩ := (binary_iff _ _ _ rfl).mp r₂; subst s₅
  obtain ⟨out,h₃,e₆⟩ := (exponential_iff _ _ _ rfl).mp r₃; subst s₆
  have e₇ := store_result st vd; subst s₇
  subst t
  refine ⟨out,⟨negative,shifted,product,?_,?_,?_,?_⟩,?_⟩
  · simpa [write,ShiftedExp.negate,Operand32.eval,Scalar.update] using h₀
  · simpa [write,ShiftedExp.negate,ShiftedExp.shift,Operand32.eval,Scalar.update] using h₁
  · simpa [write,ShiftedExp.negate,ShiftedExp.shift,ShiftedExp.convert,Operand32.eval,Scalar.update] using h₂
  · simpa [write,ShiftedExp.negate,ShiftedExp.shift,ShiftedExp.convert,ShiftedExp.exponential,Operand32.eval,Scalar.update] using h₃
  · simp only [Frame,save,write,ShiftedExp.negate,ShiftedExp.shift,ShiftedExp.convert,ShiftedExp.exponential,Scalar.update,start]
    simp only [List.length_set,true_and,ite_true]
    intro r h0 h1 h2
    simp [h0,h1,h2]

/-- Every allowed arithmetic outcome can be realized by the fetched memory stage. -/
theorem normalize_realize (target : Ptx.Target) (s : Scalar.State) (a b dst : Nat) (out : Word)
    (supported : Scalar.Binary32.SupportedTarget target) (start : s.pc=0)
    (va : ValidIndex s.memory a) (vb : ValidIndex s.memory b) (vd : ValidIndex s.memory dst)
    (allowed : NormalizeStages s.memory[a]! s.memory[b]! out) :
    ∃ t, Run target (normalizeProgram a b dst) s t ∧ t.memory=s.memory.set dst out := by
  obtain ⟨inv,h0,h1⟩ := allowed
  let s₁ := write s 0 s.memory[a]!
  let s₂ := write s₁ 1 s.memory[b]!
  let u3 := write s₂ 2 inv
  let u4 := write u3 2 out
  let t := save u4 dst
  have l₀ : Eval (load 0 a) s s₁ := (load_iff s s₁ 0 a va).mpr rfl
  have l₁ : Eval (load 1 b) s₁ s₂ := (load_iff s₁ s₂ 1 b vb).mpr rfl
  have hstep0 : Eval (.reciprocal (Normalize.reciprocal 1 2)) s₂ u3 := by
    apply (reciprocal_iff _ _ _ rfl).mpr
    refine ⟨inv,?_,rfl⟩
    simpa [s₁,s₂,u3,u4,write,Scalar.update,Operand32.eval,Normalize.reciprocal] using h0
  have hstep1 : Eval (.binary (Normalize.multiply 0 2)) u3 u4 := by
    apply (binary_iff _ _ _ rfl).mpr
    refine ⟨out,?_,rfl⟩
    simpa [s₁,s₂,u3,u4,write,Scalar.update,Operand32.eval,Normalize.multiply] using h1
  have st : Eval (store dst 2) u4 t := (store_iff u4 t dst vd).mpr rfl
  refine ⟨t,⟨supported,start,?_⟩,?_⟩
  · apply Executes.cons ?_ l₀
    apply Executes.cons ?_ l₁
    apply Executes.cons ?_ hstep0
    apply Executes.cons ?_ hstep1
    refine Executes.cons ?_ st (.nil _)
    all_goals simp [normalizeProgram,s₁,s₂,u3,u4,write,start]
  · simp [t,save,s₁,s₂,u3,u4,write,Scalar.update]

/-- Every allowed arithmetic outcome can be realized by the fetched memory stage. -/
theorem shifted_realize (target : Ptx.Target) (s : Scalar.State) (a b dst : Nat) (out : Word)
    (supported : Scalar.Binary32.SupportedTarget target) (start : s.pc=0)
    (va : ValidIndex s.memory a) (vb : ValidIndex s.memory b) (vd : ValidIndex s.memory dst)
    (allowed : ShiftedStages s.memory[a]! s.memory[b]! out) :
    ∃ t, Run target (shiftedProgram a b dst) s t ∧ t.memory=s.memory.set dst out := by
  obtain ⟨negative,shifted,product,h0,h1,h2,h3⟩ := allowed
  let s₁ := write s 0 s.memory[a]!
  let s₂ := write s₁ 1 s.memory[b]!
  let u3 := write s₂ 2 negative
  let u4 := write u3 2 shifted
  let u5 := write u4 2 product
  let u6 := write u5 2 out
  let t := save u6 dst
  have l₀ : Eval (load 0 a) s s₁ := (load_iff s s₁ 0 a va).mpr rfl
  have l₁ : Eval (load 1 b) s₁ s₂ := (load_iff s₁ s₂ 1 b vb).mpr rfl
  have hstep0 : Eval (.binary (ShiftedExp.negate 1 2)) s₂ u3 := by
    apply (binary_iff _ _ _ rfl).mpr
    refine ⟨negative,?_,rfl⟩
    simpa [s₁,s₂,u3,u4,u5,u6,write,Scalar.update,Operand32.eval,ShiftedExp.negate] using h0
  have hstep1 : Eval (.binary (ShiftedExp.shift 0 2)) u3 u4 := by
    apply (binary_iff _ _ _ rfl).mpr
    refine ⟨shifted,?_,rfl⟩
    simpa [s₁,s₂,u3,u4,u5,u6,write,Scalar.update,Operand32.eval,ShiftedExp.shift] using h1
  have hstep2 : Eval (.binary (ShiftedExp.convert 2)) u4 u5 := by
    apply (binary_iff _ _ _ rfl).mpr
    refine ⟨product,?_,rfl⟩
    simpa [s₁,s₂,u3,u4,u5,u6,write,Scalar.update,Operand32.eval,ShiftedExp.convert] using h2
  have hstep3 : Eval (.exponential (ShiftedExp.exponential 2)) u5 u6 := by
    apply (exponential_iff _ _ _ rfl).mpr
    refine ⟨out,?_,rfl⟩
    simpa [s₁,s₂,u3,u4,u5,u6,write,Scalar.update,Operand32.eval,ShiftedExp.exponential] using h3
  have st : Eval (store dst 2) u6 t := (store_iff u6 t dst vd).mpr rfl
  refine ⟨t,⟨supported,start,?_⟩,?_⟩
  · apply Executes.cons ?_ l₀
    apply Executes.cons ?_ l₁
    apply Executes.cons ?_ hstep0
    apply Executes.cons ?_ hstep1
    apply Executes.cons ?_ hstep2
    apply Executes.cons ?_ hstep3
    refine Executes.cons ?_ st (.nil _)
    all_goals simp [shiftedProgram,s₁,s₂,u3,u4,u5,u6,write,start]
  · simp [t,save,s₁,s₂,u3,u4,u5,u6,write,Scalar.update]

/-- One invocation in an arena. Guards state the allocation and no-wrap domain;
the existential states carry actual fetched execution, not its postcondition. -/
def ShiftLaunch (target : Ptx.Target) (a b dst : Nat) (before after : List Word) : Prop :=
  ValidIndex before a ∧ ValidIndex before b ∧ ValidIndex before dst ∧
  ∃ s t, s.memory=before ∧ t.memory=after ∧ Run target (shiftedProgram a b dst) s t

def NormalizeLaunch (target : Ptx.Target) (a b dst : Nat) (before after : List Word) : Prop :=
  ValidIndex before a ∧ ValidIndex before b ∧ ValidIndex before dst ∧
  ∃ s t, s.memory=before ∧ t.memory=after ∧ Run target (normalizeProgram a b dst) s t

theorem shifted_launch_correct {target a b dst before after}
    (run : ShiftLaunch target a b dst before after) :
    ∃out, ShiftedStages before[a]! before[b]! out ∧ after=before.set dst out := by
  obtain ⟨va,vb,vd,s,t,hs,ht,run⟩ := run
  subst before; subst after
  obtain ⟨out,stages,frame⟩ := shifted_correct target s t a b dst va vb vd run
  exact ⟨out,stages,frame.2.1⟩

theorem normalize_launch_correct {target a b dst before after}
    (run : NormalizeLaunch target a b dst before after) :
    ∃out, NormalizeStages before[a]! before[b]! out ∧ after=before.set dst out := by
  obtain ⟨va,vb,vd,s,t,hs,ht,run⟩ := run
  subst before; subst after
  obtain ⟨out,stages,frame⟩ := normalize_correct target s t a b dst va vb vd run
  exact ⟨out,stages,frame.2.1⟩

/-- The states witnessing a launch also witness actual emitted-access safety. -/
theorem shifted_launch_memory_safe {target a b dst before after}
    (run : ShiftLaunch target a b dst before after) :
    after.length=before.length ∧ ∃s t, s.memory=before ∧ t.memory=after ∧
      Run target (shiftedProgram a b dst) s t ∧
      ∀effect, AccessAt (shiftedProgram a b dst) (shiftedProgram a b dst) s t effect →
        effect.address.toNat % 4=0 ∧ effect.address.toNat+4≤4*before.length := by
  obtain ⟨_,_,_,s,t,hs,ht,run⟩ := run
  have safety := run_memory_safe run
  exact ⟨ht.symm ▸ hs.symm ▸ safety.1,s,t,hs,ht,run,by simpa only [hs] using safety.2⟩

theorem normalize_launch_memory_safe {target a b dst before after}
    (run : NormalizeLaunch target a b dst before after) :
    after.length=before.length ∧ ∃s t, s.memory=before ∧ t.memory=after ∧
      Run target (normalizeProgram a b dst) s t ∧
      ∀effect, AccessAt (normalizeProgram a b dst) (normalizeProgram a b dst) s t effect →
        effect.address.toNat % 4=0 ∧ effect.address.toNat+4≤4*before.length := by
  obtain ⟨_,_,_,s,t,hs,ht,run⟩ := run
  have safety := run_memory_safe run
  exact ⟨ht.symm ▸ hs.symm ▸ safety.1,s,t,hs,ht,run,by simpa only [hs] using safety.2⟩

def entry (memory : List Word) : Scalar.State := ⟨0,fun _ => 0,fun _ => 0,fun _ => false,memory⟩

theorem shifted_launch_realize (target : Ptx.Target) (a b dst : Nat) (before : List Word) (out : Word)
    (supported : Scalar.Binary32.SupportedTarget target)
    (va : ValidIndex before a) (vb : ValidIndex before b) (vd : ValidIndex before dst)
    (allowed : ShiftedStages before[a]! before[b]! out) :
    ShiftLaunch target a b dst before (before.set dst out) := by
  obtain ⟨t,run,mem⟩ := shifted_realize target (entry before) a b dst out supported rfl va vb vd allowed
  exact ⟨va,vb,vd,entry before,t,rfl,mem,run⟩

theorem normalize_launch_realize (target : Ptx.Target) (a b dst : Nat) (before : List Word) (out : Word)
    (supported : Scalar.Binary32.SupportedTarget target)
    (va : ValidIndex before a) (vb : ValidIndex before b) (vd : ValidIndex before dst)
    (allowed : NormalizeStages before[a]! before[b]! out) :
    NormalizeLaunch target a b dst before (before.set dst out) := by
  obtain ⟨t,run,mem⟩ := normalize_realize target (entry before) a b dst out supported rfl va vb vd allowed
  exact ⟨va,vb,vd,entry before,t,rfl,mem,run⟩

theorem shifted_launch_exists (target : Ptx.Target) (a b dst : Nat) (before : List Word) (x m : ℝ)
    (supported : Scalar.Binary32.SupportedTarget target)
    (va : ValidIndex before a) (vb : ValidIndex before b) (vd : ValidIndex before dst)
    (left : Ptx.Binary32.finiteReal before[a]! = some x)
    (right : Ptx.Binary32.finiteReal before[b]! = some m)
    (bounds : Ptx.Binary32.ShiftedExp.InputBounds x m) :
    ∃after, ShiftLaunch target a b dst before after := by
  obtain ⟨negative,shifted,product,out,h₀,h₁,h₂,h₃⟩ :=
    Ptx.Binary32.ShiftedExp.stages_exist before[a]! before[b]! x m left right bounds
  exact ⟨_,shifted_launch_realize target a b dst before out supported va vb vd
    ⟨negative,shifted,product,h₀,h₁,h₂,h₃⟩⟩

theorem normalize_launch_exists (target : Ptx.Target) (a b dst : Nat) (before : List Word)
    (supported : Scalar.Binary32.SupportedTarget target)
    (va : ValidIndex before a) (vb : ValidIndex before b) (vd : ValidIndex before dst) :
    ∃after, NormalizeLaunch target a b dst before after := by
  obtain ⟨inverse,h₀⟩ := Ptx.Binary32.Reciprocal.results_exists before[b]!
  obtain ⟨out,h₁⟩ := Ptx.Binary32.results_exists .mul before[a]! inverse
  exact ⟨_,normalize_launch_realize target a b dst before out supported va vb vd ⟨inverse,h₀,h₁⟩⟩

/-- A constant store is a fetched scalar store with an immediate word operand. -/
def constantStore (index : Nat) (word : Word) : Instr :=
  .scalar (.plain (.store (.imm (address index)) (.imm word)))

def StoreLaunch (target : Ptx.Target) (index : Nat) (word : Word) (before after : List Word) : Prop :=
  ValidIndex before index ∧ ∃s t, s.memory=before ∧ t.memory=after ∧
    Run target [constantStore index word] s t

theorem constantStore_iff (s t : Scalar.State) (index : Nat) (word : Word)
    (valid : ValidIndex s.memory index) :
    Eval (constantStore index word) s t ↔ t={s with pc:=s.pc+1,memory:=s.memory.set index word} := by
  constructor
  · intro h; cases h with
    | scalar step =>
      simp [Scalar.eval,Scalar.Instr.plain,Scalar.Guard.eval,Scalar.Operand64.eval,
        Scalar.Operand32.eval,address_index _ _ valid] at step
      exact step.1.symm
  · rintro rfl
    apply Eval.scalar (e := Scalar.occurrence s (.plain (.store (.imm (address index)) (.imm word))) true
      (some ⟨.store,address index,word⟩))
    simp [Scalar.eval,Scalar.Instr.plain,Scalar.Guard.eval,Scalar.Operand64.eval,
      Scalar.Operand32.eval,address_index _ _ valid]

theorem store_launch_correct {target index word before after}
    (run : StoreLaunch target index word before after) : after=before.set index word := by
  obtain ⟨valid,s,t,hs,ht,_,_,trace⟩ := run
  subst before; subst after
  obtain ⟨middle,_,step,last⟩ := executes_cons.mp trace
  have last := executes_nil.mp last
  subst t
  exact congrArg Scalar.State.memory ((constantStore_iff _ _ _ _ valid).mp step)

theorem store_launch_exists (target : Ptx.Target) (index : Nat) (word : Word) (before : List Word)
    (supported : Scalar.Binary32.SupportedTarget target) (valid : ValidIndex before index) :
    StoreLaunch target index word before (before.set index word) := by
  let s := entry before
  let t : Scalar.State := {s with pc:=1,memory:=before.set index word}
  refine ⟨valid,s,t,rfl,rfl,supported,rfl,?_⟩
  exact Executes.cons rfl ((constantStore_iff s t index word valid).mpr rfl) (.nil _)

theorem store_launch_memory_safe {target index word before after}
    (run : StoreLaunch target index word before after) :
    after.length=before.length ∧ ∃s t, s.memory=before ∧ t.memory=after ∧
      Run target [constantStore index word] s t ∧
      ∀effect, AccessAt [constantStore index word] [constantStore index word] s t effect →
        effect.address.toNat % 4=0 ∧ effect.address.toNat+4≤4*before.length := by
  obtain ⟨_,s,t,hs,ht,run⟩ := run
  have safety := run_memory_safe run
  exact ⟨ht.symm ▸ hs.symm ▸ safety.1,s,t,hs,ht,run,by simpa only [hs] using safety.2⟩

end Ptx.Scalar.SoftmaxMemory

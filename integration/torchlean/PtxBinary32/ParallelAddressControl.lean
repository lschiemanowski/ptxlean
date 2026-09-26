import PtxBinary32.ParallelControl

/-! A projection retaining address-control state, not tensor data. Compatibility
is proved against fetched instructions before this projection is used for a
kernel. It imposes no restrictions on candidate load values or binary32 results. -/
namespace Ptx.Scalar.Parallel.AddressControl

def Visible (r : Nat) : Prop := r=0 ∨ r=1 ∨ r=2 ∨ r=3 ∨ r=7
instance (r : Nat) : Decidable (Visible r) := inferInstanceAs (Decidable (_ ∨ _ ∨ _ ∨ _ ∨ _))

structure Agree (actual model : Scalar.State) : Prop where
  pc : actual.pc=model.pc
  regs : ∀ r, Visible r → actual.regs r=model.regs r
  addrs : actual.addrs=model.addrs
  pred : actual.preds 0=model.preds 0

def advance (s : Scalar.State) : Scalar.State := {s with pc := s.pc+1}

def scalar (op : Scalar.Op) (s : Scalar.State) : Scalar.State :=
  let next := advance s
  match op with
  | .mov32 d a => {next with regs := Scalar.update s.regs d (a.eval s)}
  | .bin32 op d a b => {next with regs := Scalar.update s.regs d (op.eval (a.eval s) (b.eval s))}
  | .mov64 d a => {next with addrs := Scalar.update s.addrs d (a.eval s)}
  | .add64 d a b => {next with addrs := Scalar.update s.addrs d (a.eval s+b.eval s)}
  | .cvt64 d a => {next with addrs := Scalar.update s.addrs d (BitVec.ofNat 64 (a.eval s).toNat)}
  | .setp op d a b => {next with preds := Scalar.update s.preds d (op.eval (a.eval s) (b.eval s))}
  | _ => next

def instruction (i : Instr) (s : Scalar.State) : Scalar.State :=
  match i with
  | .localStep i | .memory _ i => scalar i.op s
  | .binary32 _ | .sync _ => advance s
  | .exit => s

def Known : Scalar.Operand32 → Prop
  | .imm _ => True
  | .reg r => Visible r

/-- Guarded data writes may be omitted; any retained update must read retained
state and execute unconditionally. Memory writes never alter this projection. -/
def Allowed (i : Scalar.Instr) : Prop :=
  match i.op with
  | .mov32 d a => Visible d → i.guard=.always ∧ Known a
  | .bin32 _ d a b => Visible d → i.guard=.always ∧ Known a ∧ Known b
  | .mov64 _ _ | .add64 _ _ _ => i.guard=.always
  | .cvt64 _ a => i.guard=.always ∧ Known a
  | .setp _ d a b => d=0 → i.guard=.always ∧ Known a ∧ Known b
  | .load d _ => ¬Visible d
  | .store _ _ => True
  | _ => False

def Compatible : Instr → Prop
  | .localStep i | .memory _ i => Allowed i
  | .binary32 i => ¬Visible i.destination
  | .sync _ | .exit => True

def ProgramCompatible (program : List Instr) : Prop := ∀ i ∈ program, Compatible i

theorem agree_refl (s : Scalar.State) : Agree s s := ⟨rfl,fun _ _ => rfl,rfl,rfl⟩

theorem agree_advance (h : Agree a b) : Agree (advance a) (advance b) :=
  ⟨congrArg (·+1) h.pc,h.regs,h.addrs,h.pred⟩

theorem agree_word (h : Agree a b) (d : Nat) (v w : Word) (same : Visible d → v=w) :
    Agree {a with regs := Scalar.update a.regs d v} {b with regs := Scalar.update b.regs d w} := by
  refine ⟨h.pc,?_,h.addrs,h.pred⟩
  intro r visible
  by_cases eq : r=d
  · subst r; simp [Scalar.update,same visible]
  · simp [Scalar.update,eq,h.regs r visible]

theorem agree_word_left (h : Agree a b) (d : Nat) (v : Word) (hidden : ¬Visible d) :
    Agree {a with regs := Scalar.update a.regs d v} b := by
  refine ⟨h.pc,?_,h.addrs,h.pred⟩
  intro r hr
  have ne : r≠d := by intro eq; subst r; exact hidden hr
  simp [Scalar.update,ne,h.regs r hr]

theorem agree_word_right (h : Agree a b) (d : Nat) (v : Word) (hidden : ¬Visible d) :
    Agree a {b with regs := Scalar.update b.regs d v} := by
  refine ⟨h.pc,?_,h.addrs,h.pred⟩
  intro r hr
  have ne : r≠d := by intro eq; subst r; exact hidden hr
  simp [Scalar.update,ne,h.regs r hr]

theorem agree_address (h : Agree a b) (d : Nat) (v : Scalar.Address) :
    Agree {a with addrs := Scalar.update a.addrs d v} {b with addrs := Scalar.update b.addrs d v} :=
  ⟨h.pc,h.regs,by rw [h.addrs],h.pred⟩

theorem agree_predicate (h : Agree a b) (d : Nat) (v w : Bool) (same : d=0 → v=w) :
    Agree {a with preds := Scalar.update a.preds d v} {b with preds := Scalar.update b.preds d w} := by
  refine ⟨h.pc,h.regs,h.addrs,?_⟩
  by_cases eq : d=0
  · subst d; simp [Scalar.update,same rfl]
  · simp [Scalar.update,Ne.symm eq,h.pred]

theorem agree_predicate_right (h : Agree a b) (d : Nat) (v : Bool) (hidden : d≠0) :
    Agree a {b with preds := Scalar.update b.preds d v} := by
  exact ⟨h.pc,h.regs,h.addrs,by simp [Scalar.update,Ne.symm hidden,h.pred]⟩

theorem operand32_eq (h : Agree a b) (operand : Scalar.Operand32) (known : Known operand) :
    operand.eval a=operand.eval b := by
  cases operand with
  | imm _ => rfl
  | reg r => exact h.regs r known

theorem operand64_eq (h : Agree a b) (operand : Scalar.Operand64) : operand.eval a=operand.eval b := by
  cases operand <;> simp [Scalar.Operand64.eval,h.addrs]

/-- The actual load candidates need not equal the model's omitted data. -/
theorem scalar_agrees (i : Scalar.Instr) (allowed : Allowed i) (h : Agree actual model)
    (evaluated : Scalar.eval candidate i actual = .next next event) : Agree next (scalar i.op model) := by
  rcases i with ⟨guard,op⟩
  cases op with
  | mov32 d a =>
    by_cases tracked : Visible d
    · obtain ⟨rfl,known⟩ := allowed tracked
      simp only [Scalar.eval,Scalar.Guard.eval,↓reduceIte] at evaluated
      obtain ⟨rfl,rfl⟩ := Scalar.StepResult.next.inj evaluated
      exact agree_word (agree_advance h) d _ _ (fun _ => operand32_eq h a known)
    · cases enabled : guard.eval actual <;> simp only [Scalar.eval,enabled,↓reduceIte] at evaluated
      · obtain ⟨rfl,rfl⟩ := Scalar.StepResult.next.inj evaluated
        exact agree_word_right (agree_advance h) d _ tracked
      · obtain ⟨rfl,rfl⟩ := Scalar.StepResult.next.inj evaluated
        exact agree_word (agree_advance h) d _ _ (fun ht => False.elim (tracked ht))
  | bin32 op d a b =>
    by_cases tracked : Visible d
    · obtain ⟨rfl,ka,kb⟩ := allowed tracked
      simp only [Scalar.eval,Scalar.Guard.eval,↓reduceIte] at evaluated
      obtain ⟨rfl,rfl⟩ := Scalar.StepResult.next.inj evaluated
      apply agree_word (agree_advance h) d _ _
      intro _; rw [operand32_eq h a ka,operand32_eq h b kb]
    · cases enabled : guard.eval actual <;> simp only [Scalar.eval,enabled,↓reduceIte] at evaluated
      · obtain ⟨rfl,rfl⟩ := Scalar.StepResult.next.inj evaluated
        exact agree_word_right (agree_advance h) d _ tracked
      · obtain ⟨rfl,rfl⟩ := Scalar.StepResult.next.inj evaluated
        exact agree_word (agree_advance h) d _ _ (fun ht => False.elim (tracked ht))
  | mov64 d a =>
    have eq : guard=.always := allowed
    subst guard
    simp only [Scalar.eval,Scalar.Guard.eval,↓reduceIte] at evaluated
    obtain ⟨rfl,rfl⟩ := Scalar.StepResult.next.inj evaluated
    simp only [scalar,operand64_eq h a]
    exact agree_address (agree_advance h) d _
  | add64 d a b =>
    have eq : guard=.always := allowed
    subst guard
    simp only [Scalar.eval,Scalar.Guard.eval,↓reduceIte] at evaluated
    obtain ⟨rfl,rfl⟩ := Scalar.StepResult.next.inj evaluated
    simp only [scalar,operand64_eq h a,operand64_eq h b]
    exact agree_address (agree_advance h) d _
  | cvt64 d a =>
    obtain ⟨rfl,known⟩ := allowed
    simp only [Scalar.eval,Scalar.Guard.eval,↓reduceIte] at evaluated
    obtain ⟨rfl,rfl⟩ := Scalar.StepResult.next.inj evaluated
    simp only [scalar,operand32_eq h a known]
    exact agree_address (agree_advance h) d _
  | setp op d a b =>
    by_cases tracked : d=0
    · obtain ⟨rfl,ka,kb⟩ := allowed tracked
      simp only [Scalar.eval,Scalar.Guard.eval,↓reduceIte] at evaluated
      obtain ⟨rfl,rfl⟩ := Scalar.StepResult.next.inj evaluated
      apply agree_predicate (agree_advance h) d _ _
      intro _; rw [operand32_eq h a ka,operand32_eq h b kb]
    · cases enabled : guard.eval actual <;> simp only [Scalar.eval,enabled,↓reduceIte] at evaluated
      · obtain ⟨rfl,rfl⟩ := Scalar.StepResult.next.inj evaluated
        exact agree_predicate_right (agree_advance h) d _ tracked
      · obtain ⟨rfl,rfl⟩ := Scalar.StepResult.next.inj evaluated
        exact agree_predicate (agree_advance h) d _ _ (fun ht => False.elim (tracked ht))
  | load d a =>
    cases enabled : guard.eval actual <;> simp only [Scalar.eval,enabled,↓reduceIte] at evaluated
    · obtain ⟨rfl,rfl⟩ := Scalar.StepResult.next.inj evaluated
      exact agree_advance h
    · split at evaluated
      · contradiction
      · obtain ⟨rfl,rfl⟩ := Scalar.StepResult.next.inj evaluated
        exact agree_word_left (agree_advance h) d _ allowed
  | store a v =>
    cases enabled : guard.eval actual <;> simp only [Scalar.eval,enabled,↓reduceIte] at evaluated
    · obtain ⟨rfl,rfl⟩ := Scalar.StepResult.next.inj evaluated
      exact agree_advance h
    · split at evaluated
      · contradiction
      · obtain ⟨rfl,rfl⟩ := Scalar.StepResult.next.inj evaluated
        exact ⟨congrArg (·+1) h.pc,h.regs,h.addrs,h.pred⟩
  | _ => contradiction

def evaluate (code : List Instr) (s : Scalar.State) : Scalar.State :=
  code.foldl (fun state i => instruction i state) s

def atPC (program : List Instr) (seed : Scalar.State) (pc : Nat) : Scalar.State :=
  evaluate (program.take pc) seed

theorem evaluate_append (left right : List Instr) (s : Scalar.State) :
    evaluate (left++right) s=evaluate right (evaluate left s) := by simp [evaluate,List.foldl_append]

theorem atPC_succ (program : List Instr) (seed : Scalar.State) (pc : Nat) (i : Instr)
    (fetch : program[pc]?=some i) : atPC program seed (pc+1)=instruction i (atPC program seed pc) := by
  simp [atPC,List.take_add_one,fetch,evaluate]

theorem scalar_pc (op : Scalar.Op) (s : Scalar.State) : (scalar op s).pc=s.pc+1 := by
  cases op <;> rfl

/-- Each lane agrees at its actual program counter; other threads' tensor
stores and arbitrary load candidates do not enter the calculation. -/
def Invariant (program : List Instr) (seeds : Fin n → Scalar.State) (s : State n) : Prop :=
  ∀ t, Agree (s.lanes t).scalar (atPC program (seeds t) (s.lanes t).scalar.pc)

private theorem install {s : State n} {seeds : Fin n → Scalar.State} (inv : Invariant program seeds s) (t : Fin n) (lane : Lane)
    (same : Agree lane.scalar (atPC program (seeds t) lane.scalar.pc)) :
    Invariant program seeds (setLane s t lane) := by
  intro u
  by_cases eq : u=t
  · subst u; simpa [setLane] using same
  · simpa [setLane,Function.update,eq] using inv u

private theorem no_halt (i : Scalar.Instr) (allowed : Allowed i) : Scalar.eval candidate i s ≠ .halted next event := by
  rcases i with ⟨guard,op⟩
  cases op <;> simp only [Allowed] at allowed
  all_goals cases enabled : guard.eval s <;> simp only [Scalar.eval,enabled,↓reduceIte]
  all_goals first | (solve | simp) | (split <;> simp)

private theorem scalar_invariant {s : State n} {seeds : Fin n → Scalar.State} (inv : Invariant program seeds s) (selected : Fin n) (space : Option Space)
    (i : Scalar.Instr) (allowed : Allowed i)
    (fetch : program[(s.lanes selected).scalar.pc]?=some wrapped)
    (model : ∀ state, instruction wrapped state=scalar i.op state) :
    Invariant program seeds (scalarStep candidate selected space i s).state := by
  have old := inv selected
  have input : Agree {(s.lanes selected).scalar with memory := arena s space}
      (atPC program (seeds selected) (s.lanes selected).scalar.pc) := ⟨old.pc,old.regs,old.addrs,old.pred⟩
  cases ev : Scalar.eval candidate i {(s.lanes selected).scalar with memory := arena s space} with
  | next next event =>
    have result := scalar_agrees i allowed input ev
    have pc : next.pc=(s.lanes selected).scalar.pc+1 := by
      have h := result.pc; rw [scalar_pc,← old.pc] at h; exact h
    have nextInv : Agree next (atPC program (seeds selected) next.pc) := by
      rw [pc,atPC_succ program (seeds selected) _ wrapped fetch,model]; exact result
    have installed := install inv selected {s.lanes selected with scalar := next} nextInv
    cases space with
    | none => simpa only [scalarStep,ev] using installed
    | some space => cases space <;> simpa only [scalarStep,ev,Invariant,setLane] using installed
  | halted next event => exact False.elim (no_halt i allowed ev)
  | fault reason => simpa only [scalarStep,ev] using inv
  | unsupported spelling => simpa only [scalarStep,ev] using inv

private theorem sync_invariant (cfg : Config n) (s : State n) (t : Fin n) (resource : Fin 16)
    (inv : Invariant program seeds s) (aligned : Aligned s)
    (fetch : program[(s.lanes t).scalar.pc]?=some (.sync resource)) :
    Invariant program seeds (synchronize cfg s t resource).state := by
  cases hd : (Barrier.step (barrierConfig cfg s t) s.barrier (barrierRequest cfg s t resource)).disposition with
  | rejectedWrongKey => simpa only [synchronize,hd] using inv
  | waiting => simpa only [synchronize,hd,Invariant] using inv
  | released =>
    have pcs := release_aligned cfg s t resource aligned hd
    simp only [synchronize,hd]
    intro u
    change Agree (advance (s.lanes u).scalar) (atPC program (seeds u) ((s.lanes u).scalar.pc+1))
    rw [atPC_succ program (seeds u) _ (.sync resource) (by rw [pcs]; exact fetch)]
    exact agree_advance (inv u)

theorem dispatch_invariant (step : Dispatch cfg candidate t i s out)
    (compatible : Compatible i) (fetch : program[(s.lanes t).scalar.pc]?=some i)
    (inv : Invariant program seeds s) (aligned : Aligned s) : Invariant program seeds out.state := by
  cases step with
  | localStep => exact scalar_invariant inv _ _ _ compatible fetch (fun _ => rfl)
  | memory => exact scalar_invariant inv _ _ _ compatible fetch (fun _ => rfl)
  | binary32 ev =>
    rename_i inst next event
    have old := inv t
    have same : Agree next (atPC program (seeds t) next.pc) := by
      rw [(Scalar.Binary32.eval_frame _ _ _ _ ev).1,atPC_succ program (seeds t) _ _ fetch]
      cases ev with
      | skipped _ => exact agree_advance old
      | executed _ _ => exact agree_word_left (agree_advance old) _ _ compatible
    exact install inv t _ same
  | sync => exact sync_invariant _ _ _ _ inv aligned fetch
  | exit => exact install inv t _ (inv t)

theorem step_invariant (step : Step cfg program candidate t s out)
    (compatible : ProgramCompatible program) (inv : Invariant program seeds s) (aligned : Aligned s) :
    Invariant program seeds out.state := by
  have h := step.2
  split at h
  · subst out; exact inv
  · split at h
    · subst out; exact inv
    · split at h
      · subst out; exact inv
      · exact dispatch_invariant h (compatible _ (List.mem_of_getElem? (by assumption))) (by assumption) inv aligned

theorem runs_invariant (run : Runs cfg program s events final) (compatible : ProgramCompatible program)
    (inv : Invariant program seeds s) (aligned : Aligned s) : Invariant program seeds final := by
  induction run with
  | nil => exact inv
  | cons step _ ih => exact ih (step_invariant step compatible inv aligned) (step_aligned step aligned)

end Ptx.Scalar.Parallel.AddressControl

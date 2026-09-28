import PoissonPTX.ContractionFetched

/-! Binary64 shared stores from the generated cell body. These are concrete
instruction effects; publication to other threads requires a separate proof. -/
namespace PtxTorchLean.Poisson.PTX.SharedStore

/-- The generated lane register is 14; registers 1 and 2 are address scratch. -/
def code (offset : Word) (src : Nat) : List Op :=
  [.wide8 1 (.reg 14), .add64 2 (.reg 3) (.reg 1),
   .store64 .shared (.offset 2 offset) (.reg src)]

def location (s : State) (offset : Word) : Word := s.regs 3 + wide s 14 + offset

def finish (s : State) (offset : Word) (src : Nat) : State :=
  put (assign (assign s 1 (wide s 14)) 2 (s.regs 3 + wide s 14))
    .shared (location s offset).toNat (s.regs src)

def Valid (s : State) (offset : Word) : Prop :=
  Valid64 s.sharedStart s.sharedBytes (location s offset).toNat

theorem run_store (s : State) (offset : Word) (src : Nat)
    (h1 : src≠1) (h2 : src≠2) (valid : Valid s offset) :
    run (code offset src) s = some (finish s offset src) := by
  simp_all [Valid,code,run,eval,Operand.eval,finish,location,wide,assign,advance,
    State.start,State.bytes,Contraction.wide_byte_offset]

theorem block_eq (execution : Block (code offset src) s t)
    (h1 : src≠1) (h2 : src≠2) (valid : Valid s offset) :
    t = finish s offset src := by
  exact Option.some.inj ((block_complete execution (by simp [code,noFP])).symm.trans
    (run_store s offset src h1 h2 valid))

/-- Every completed fetched store block writes the original source word. -/
theorem fetched_correct (pre suffix : List Op) (pc : s.pc=pre.length)
    (execution : Runs (pre++code offset src++suffix) s t)
    (done : t.pc=pre.length+(code offset src).length)
    (h1 : src≠1) (h2 : src≠2) (valid : Valid s offset) :
    t.shared = write64 s.shared (location s offset).toNat (s.regs src) ∧
    t.global = s.global ∧
    (∀ r, r≠1 → r≠2 → t.regs r=s.regs r) := by
  rw [block_eq (Contraction.fetched_block _ _ _ execution pc done) h1 h2 valid]
  refine ⟨rfl,rfl,?_⟩
  intro r hr1 hr2
  simp [finish,put,assign,advance,hr1,hr2]

theorem fetched_exists (s : State) (pre suffix : List Op) (pc : s.pc=pre.length)
    (h1 : src≠1) (h2 : src≠2) (valid : Valid s offset) :
    ∃ t, Runs (pre++code offset src++suffix) s t ∧
      t.pc=pre.length+(code offset src).length := by
  have hb := run_sound (run_store s offset src h1 h2 valid)
  exact ⟨_,block_fetched hb pre suffix pc,by rw [block_pc hb,pc]⟩

/-- Address arithmetic remains modular in the instruction semantics. -/
theorem location_exact (s : State) (offset : Word)
    (lane : (s.regs 14).toNat < 2^32)
    (bound : (s.regs 3).toNat+(s.regs 14).toNat*8+offset.toNat < 2^64) :
    (location s offset).toNat = (s.regs 3).toNat+(s.regs 14).toNat*8+offset.toNat := by
  have wideBound : (s.regs 14).toNat*8 < 2^64 := by omega
  have baseBound : (s.regs 3).toNat+(s.regs 14).toNat*8 < 2^64 := by omega
  simp only [location,wide,BitVec.toNat_add,BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt lane,Nat.mod_eq_of_lt wideBound,
    Nat.mod_eq_of_lt baseBound,Nat.mod_eq_of_lt bound]

/-- Seven planes of at most 25 words fit in the generated shared allocation. -/
theorem valid_of_plane (s : State) (width : Nat) (plane : Fin 7)
    (hw : width≤5) (lane : (s.regs 14).toNat < width*width)
    (base : (s.regs 3).toNat=s.sharedStart) (aligned : s.sharedStart%8=0)
    (fits : 7*width*width*8≤s.sharedBytes)
    (noWrap : s.sharedStart+s.sharedBytes≤2^64) :
    Valid s (BitVec.ofNat 64 (plane.val*width*width*8)) := by
  have hp := plane.isLt
  have hsmall : width*width≤25 := by nlinarith
  have po : plane.val*width*width*8 < 2^64 := by nlinarith
  have endBound : (s.regs 14).toNat*8+plane.val*width*width*8+8≤7*width*width*8 := by
    have h := Nat.mul_le_mul_right (width*width) (show plane.val+1≤7 by omega)
    nlinarith
  have hb : (s.regs 3).toNat+(s.regs 14).toNat*8+
      (BitVec.ofNat 64 (plane.val*width*width*8)).toNat < 2^64 := by
    rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt po,base]; omega
  unfold Valid
  rw [location_exact s _ (by omega) hb,BitVec.toNat_ofNat,Nat.mod_eq_of_lt po,base]
  exact ⟨by omega,by simp [Nat.add_mod,aligned],by omega,noWrap⟩

/-- A register is untouched unless it is an explicit destination. -/
def keeps (r : Nat) : Op → Prop
  | .mov d _ | .mul32 d _ _ | .add32 d _ _ | .add64 d _ _ |
    .wide8 d _ | .load64 _ d _ | .fp _ d _ _ => r≠d
  | .store64 _ _ _ => True

theorem eval_keeps (h : Eval op s t) (frame : keeps r op) : t.regs r=s.regs r := by
  cases h <;> simp_all [keeps,assign,advance,put]
  case store64 => cases ‹Space› <;> rfl

theorem block_keeps (h : Block ops s t) (frame : ∀ op∈ops, keeps r op) :
    t.regs r=s.regs r := by
  induction h with
  | nil => rfl
  | cons he hb ih =>
    exact (ih (fun op ho => frame op (by simp [ho]))).trans (eval_keeps he (frame _ (by simp)))

theorem contraction_keeps_lane (h : Block (Contraction.program width acc a b) s t)
    (allowed : Contraction.Accumulator acc) : t.regs 14=s.regs 14 := by
  apply block_keeps h
  rcases allowed with rfl | rfl
  all_goals
    simp only [Contraction.program,Contraction.terms,List.forall_mem_cons,
      List.forall_mem_flatMap]
    constructor
    · simp [keeps]
    · intro k hk
      cases ha : a.space <;> cases hb : b.space <;>
        simp [Contraction.term,Contraction.loadCode,Contraction.indexCode,Contraction.mac,
          ha,hb,keeps]

/-- Publication address and bounds survive a contraction, including the lane
register omitted by its narrower matrix-operand environment. -/
theorem contraction_valid (h : Block (Contraction.program width acc a b) s t)
    (allowed : Contraction.Accumulator acc) (stable : Contraction.Stable s t) :
    location t offset=location s offset ∧ (Valid t offset ↔ Valid s offset) := by
  have lane := contraction_keeps_lane h allowed
  simp only [Contraction.Stable,Contraction.environment,Prod.mk.injEq] at stable
  rcases stable with ⟨hg,hs,hgs,hgb,hss,hsb,h0,h3,h16,h17⟩
  simp [location,wide,lane,h3,Valid,hss,hsb]

/-- The adjacent contraction and store block derives its stored scalar from
TorchLean's actual ordered matrix product, rather than a phase-result premise. -/
theorem contraction_store (allowed : Contraction.Accumulator acc)
    (loads : ∀ k<width, Contraction.Valid s width k a ∧ Contraction.Valid s width k b)
    (valid : Valid s offset)
    (execution : Block (Contraction.program width acc a b ++ code offset acc) s t) :
    decode (read64 t.shared (location s offset).toNat) =
      Spec.get2 (Spec.matMulSpec (Contraction.leftTensor s width a)
        (Contraction.rightTensor s width b)) 0 0 ∧ t.global=s.global := by
  obtain ⟨u,hc,hs⟩ := block_split _ _ execution
  obtain ⟨result,stable⟩ := Contraction.correct allowed loads hc
  obtain ⟨address,storeValid⟩ := contraction_valid hc allowed stable (offset:=offset)
  have h1 : acc≠1 := by rcases allowed with rfl | rfl <;> decide
  have h2 : acc≠2 := by rcases allowed with rfl | rfl <;> decide
  rw [block_eq hs h1 h2 (storeValid.mpr valid)]
  constructor
  · simp only [finish,put,advance,assign,address,read64_write64]
    rw [Contraction.tensor_fold]
    exact result
  · exact congrArg Prod.fst stable

theorem contraction_store_exists (s : State) (allowed : Contraction.Accumulator acc)
    (loads : ∀ k<width, Contraction.Valid s width k a ∧ Contraction.Valid s width k b)
    (valid : Valid s offset) :
    ∃ t, Block (Contraction.program width acc a b ++ code offset acc) s t := by
  obtain ⟨u,hc⟩ := Contraction.exists_execution s allowed loads
  have stable := (Contraction.correct allowed loads hc).2
  have hv := (contraction_valid hc allowed stable (offset:=offset)).2.mpr valid
  have h1 : acc≠1 := by rcases allowed with rfl | rfl <;> decide
  have h2 : acc≠2 := by rcases allowed with rfl | rfl <;> decide
  exact ⟨_,block_append hc (run_sound (run_store u offset acc h1 h2 hv))⟩

theorem fetched_contraction_store (allowed : Contraction.Accumulator acc)
    (loads : ∀ k<width, Contraction.Valid s width k a ∧ Contraction.Valid s width k b)
    (valid : Valid s offset) (pre suffix : List Op) (pc : s.pc=pre.length)
    (execution : Runs (pre++(Contraction.program width acc a b ++ code offset acc)++suffix) s t)
    (done : t.pc=pre.length+(Contraction.program width acc a b ++ code offset acc).length) :
    decode (read64 t.shared (location s offset).toNat) =
      Spec.get2 (Spec.matMulSpec (Contraction.leftTensor s width a)
        (Contraction.rightTensor s width b)) 0 0 ∧ t.global=s.global :=
  contraction_store allowed loads valid (Contraction.fetched_block _ _ _ execution pc done)

theorem fetched_contraction_store_exists (s : State) (allowed : Contraction.Accumulator acc)
    (loads : ∀ k<width, Contraction.Valid s width k a ∧ Contraction.Valid s width k b)
    (valid : Valid s offset) (pre suffix : List Op) (pc : s.pc=pre.length) :
    ∃ t, Runs (pre++(Contraction.program width acc a b ++ code offset acc)++suffix) s t ∧
      t.pc=pre.length+(Contraction.program width acc a b ++ code offset acc).length := by
  obtain ⟨t,h⟩ := contraction_store_exists s allowed loads valid
  exact ⟨t,block_fetched h pre suffix pc,by rw [block_pc h,pc]⟩

end PtxTorchLean.Poisson.PTX.SharedStore

import PtxBinary32.MaximumProgram
import PtxBinary32.ParallelSegmentSweep

/-! Selected complete fetched execution of the parallel maximum. The witness
uses concrete array reads and derives an admitted graph for that same trace. -/
namespace Ptx.Scalar.Parallel.Maximum
set_option maxRecDepth 12000
set_option maxHeartbeats 4000000

abbrev nodeValue (global : List Word) (k t : Nat) :=
  Ptx.Binary32.Maximum.Tree.nodeValue (fun i => global[i]!) k t

private theorem eligible (d : Nat) : Mixed.Eligible (config d).target := by
  change 94=94 ∧ 70≤70; decide

private theorem four (x : Nat) : (x+x)+(x+x)=4*x := by omega
private theorem succFour (x : Nat) : 4*x+4=4*(x+1) := by omega

def publishFinish (d : Nat) (s : State (width d)) (t : Fin (width d)) :=
  (segmentReference (config d) t publishCode s).1

theorem publish_regular (b : Bounds d) (s : State (width d)) (t : Fin (width d))
    (tid : (s.lanes t).scalar.regs 0=BitVec.ofNat 32 t.val)
    (gb : width d+1≤s.global.length) (sb : sharedWords d≤s.shared.length) :
    SegmentRegular (config d) t publishCode s := by
  have tf : t.val<4294967296 := lt_trans t.isLt (width_fits b)
  have tp : 4*t.val<18446744073709551616 := by omega
  have g : t.val<s.global.length := by have := t.isLt; omega
  have sh : t.val<s.shared.length := by
    have h := plane_bound d 0 t.val (by omega) t.isLt
    simp only [Nat.zero_mul,Nat.zero_add] at h
    exact lt_of_lt_of_le h sb
  simp [publishCode,Dense.pointer,Dense.scalar,SegmentRegular,Reference.dispatch,
    scalarStep,Scalar.eval,Scalar.Instr.plain,Scalar.Guard.eval,Scalar.Operand32.eval,
    Scalar.Operand64.eval,Scalar.update,setLane,arena,tid,Nat.mod_eq_of_lt tf,
    ←BitVec.ofNat_add,four,Scalar.addressIndex,Nat.mod_eq_of_lt tp,g,sh]

theorem publish_effect (b : Bounds d) (s : State (width d)) (t : Fin (width d))
    (tid : (s.lanes t).scalar.regs 0=BitVec.ofNat 32 t.val)
    (gb : width d+1≤s.global.length) (sb : sharedWords d≤s.shared.length) :
    (publishFinish d s t).global=s.global ∧
    (publishFinish d s t).shared=s.shared.set t.val s.global[t.val]! ∧
    (publishFinish d s t).site=s.site ∧
    ((publishFinish d s t).lanes t).scalar.regs 0=(s.lanes t).scalar.regs 0 ∧
    (∀u,u≠t→(publishFinish d s t).lanes u=s.lanes u) := by
  have tf : t.val<4294967296 := lt_trans t.isLt (width_fits b)
  have tp : 4*t.val<18446744073709551616 := by omega
  have g : t.val<s.global.length := by have := t.isLt; omega
  have sh : t.val<s.shared.length := by
    have h := plane_bound d 0 t.val (by omega) t.isLt
    simp only [Nat.zero_mul,Nat.zero_add] at h
    exact lt_of_lt_of_le h sb
  simp [publishFinish,publishCode,Dense.pointer,Dense.scalar,segmentReference,Reference.dispatch,
    scalarStep,Scalar.eval,Scalar.Instr.plain,Scalar.Guard.eval,Scalar.Operand32.eval,
    Scalar.Operand64.eval,Scalar.update,setLane,arena,tid,Nat.mod_eq_of_lt tf,
    ←BitVec.ofNat_add,four,Scalar.addressIndex,Nat.mod_eq_of_lt tp,g,sh]
  intro u ne
  simp [Function.update,ne]

private theorem code_fetch (f : Fetches prog pc (code++tail)) : Fetches prog pc code := by
  intro k hk
  rw [f k (by simp; omega)]
  simp [List.getElem?_append,hk]

structure Ready (d : Nat) (inputs : List Word) (s : State (width d)) (k : Nat) : Prop where
  global : s.global=inputs
  extent : sharedWords d≤s.shared.length
  pc : ∀t,(s.lanes t).scalar.pc=6+24*k
  live : ∀t,(s.lanes t).halted=false
  ids : ∀t,(s.lanes t).scalar.regs 0=BitVec.ofNat 32 t.val
  barrier : s.barrier=Barrier.reset (k+1)
  site : s.site=none
  values : ∀t,t<2^(d-k)→s.shared[k*width d+t]?=some (nodeValue inputs k t)

structure PublishInvariant (d : Nat) (original current : State (width d)) (count : Nat) : Prop where
  global : current.global=original.global
  shared : current.shared.length=original.shared.length
  values : ∀t : Fin (width d),t.val<count→current.shared[t.val]?=some original.global[t.val]!
  pc : ∀t : Fin (width d),(current.lanes t).scalar.pc=if t.val<count then 5 else 0
  live : ∀t,(current.lanes t).halted=false
  ids : ∀t,(current.lanes t).scalar.regs 0=BitVec.ofNat 32 t.val
  barrier : current.barrier=Barrier.reset 0
  site : current.site=none

theorem publish_invariant_step (b : Bounds d) (original current : State (width d))
    (count : Nat) (hc : count<width d) (inv : PublishInvariant d original current count)
    (gb : width d+1≤original.global.length) (sb : sharedWords d≤original.shared.length) :
    PublishInvariant d original (publishFinish d current ⟨count,hc⟩) (count+1) := by
  let t : Fin (width d) := ⟨count,hc⟩
  have g : width d+1≤current.global.length := by simpa [inv.global] using gb
  have sh : sharedWords d≤current.shared.length := by rw [inv.shared]; exact sb
  have eff := publish_effect b current t (inv.ids t) g sh
  have frame := (segmentReference_concrete (publish_regular b current t (inv.ids t) g sh)).frame
  change ((publishFinish d current t).lanes t).scalar.pc=_ ∧
    ((publishFinish d current t).lanes t).halted=_ ∧ (publishFinish d current t).barrier=_ at frame
  have pc0 : (current.lanes t).scalar.pc=0 := by simp [inv.pc,t]
  refine ⟨eff.1.trans inv.global,?_,?_,?_,?_,?_,frame.2.2.trans inv.barrier,eff.2.2.1.trans inv.site⟩
  · rw [eff.2.1,List.length_set]; exact inv.shared
  · intro u hu
    rw [eff.2.1]
    by_cases eq : u=t
    · subst u
      have inside : t.val<current.shared.length := by
        have h := plane_bound d 0 t.val (by omega) t.isLt
        simp only [Nat.zero_mul,Nat.zero_add] at h
        exact lt_of_lt_of_le h sh
      simp [inside,inv.global]
    · have ne : t.val≠u.val := fun h => eq (Fin.ext h.symm)
      rw [List.getElem?_set_ne ne]
      exact inv.values u (by dsimp [t] at ne; omega)
  · intro u
    by_cases eq : u=t
    · subst u; simpa [t,pc0] using frame.1
    · rw [eff.2.2.2.2 u eq,inv.pc]
      have ne : u.val≠count := fun h => eq (Fin.ext h)
      have same : u.val<count+1↔u.val<count := by omega
      simp [same]
  · intro u
    by_cases eq : u=t
    · subst u; exact frame.2.1.trans (inv.live t)
    · rw [eff.2.2.2.2 u eq]; exact inv.live u
  · intro u
    by_cases eq : u=t
    · subst u; exact eff.2.2.2.1.trans (inv.ids t)
    · rw [eff.2.2.2.2 u eq]; exact inv.ids u

theorem publish_exists (b : Bounds d) (global shared : List Word) (seeds : Fin (width d)→Scalar.State)
    (gb : width d+1≤global.length) (sb : sharedWords d≤shared.length) :
    ∃events final,ConcreteRuns (config d) (program d) (initial d global shared seeds) events final ∧
      Ready d global final 0 ∧ final.shared.length=shared.length := by
  let start := initial d global shared seeds
  have sweep : ∀count,count≤width d→∃events current,
      ConcreteRuns (config d) (program d) start events current ∧ PublishInvariant d start current count := by
    intro count bound
    induction count with
    | zero =>
      refine ⟨[],start,.nil,rfl,rfl,?_,?_,?_,?_,rfl,rfl⟩
      · intro t ht; omega
      · intro t; simp [start,initial]
      · intro t; rfl
      · intro t; simp [start,initial,Scalar.update]
    | succ count ih =>
      obtain ⟨events,current,run,inv⟩ := ih (by omega)
      let t : Fin (width d) := ⟨count,by omega⟩
      have g : width d+1≤current.global.length := by rw [inv.global]; exact gb
      have sh : sharedWords d≤current.shared.length := by rw [inv.shared]; exact sb
      have seg := segmentReference_concrete (publish_regular b current t (inv.ids t) g sh)
      have pc : (current.lanes t).scalar.pc=0 := by simp [inv.pc,t]
      have tail := seg.compile (by rw [pc]; exact code_fetch (publish_fetch d)) (inv.live t)
        (by simp [inv.barrier,Barrier.reset]) (eligible d)
      exact ⟨_,_,concrete_runs_append run tail,publish_invariant_step b start current count (by omega) inv gb sb⟩
  obtain ⟨events,current,run,inv⟩ := sweep (width d) (Nat.le_refl _)
  have pcs : ∀t,(current.lanes t).scalar.pc=5 := by intro t; simp [inv.pc,t.isLt]
  have fetch : (program d)[5]?=some (.sync 0) := by
    rw [publish_fetch d 5 (by simp)]
    simp [publish,publishCode,Dense.pointer]
  obtain ⟨barriers,brun⟩ := barrier_round_concrete (config d) current (program d) 5 0 pcs inv.live inv.barrier inv.site fetch (eligible d)
  refine ⟨events++barriers,afterRound current 0,concrete_runs_append run brun,?_,inv.shared⟩
  refine ⟨inv.global,by change sharedWords d≤current.shared.length; rw [inv.shared]; exact sb,?_,inv.live,inv.ids,rfl,rfl,?_⟩
  · intro t; simp [afterRound,pcs]
  · intro t ht
    simpa [nodeValue,Ptx.Binary32.Maximum.Tree.nodeValue,afterRound,start,initial] using inv.values ⟨t,by simpa using ht⟩ ht


def leftIndex (d k : Nat) (t : Fin (width d)) := 2*t.val+k*width d
def nextIndex (d k : Nat) (t : Fin (width d)) := t.val+(k+1)*width d

theorem round_indices (b : Bounds d) (hk : k<d) (t : Fin (width d)) :
    leftIndex d k t<2^32 ∧ nextIndex d k t<sharedWords d ∧
      (t.val<2^(d-(k+1))→leftIndex d k t+1<sharedWords d) := by
  have dd := bounds_depth b
  have ww : width d≤1024 := b
  have kp : k*width d≤d*width d := Nat.mul_le_mul_right _ (by omega)
  have dp : d*width d≤10*1024 := Nat.mul_le_mul dd ww
  have tv := t.isLt
  refine ⟨?_,by simpa [nextIndex,Nat.add_comm] using plane_bound d (k+1) t.val (by omega) tv,?_⟩
  · dsimp [leftIndex]; omega
  · intro active
    have child := (children_bound k d t.val hk active).2
    have w : 2^(d-k)≤width d := Nat.pow_le_pow_right (by decide) (Nat.sub_le _ _)
    have idx := plane_bound d k (2*t.val+1) (by omega) (by omega)
    dsimp [leftIndex]; omega

def roundFinish (d k : Nat) (s : State (width d)) (t : Fin (width d)) :=
  (segmentReference (config d) t (roundCode d k) s).1

theorem round_prefix_regular (b : Bounds d) (hk : k<d) (s : State (width d)) (t : Fin (width d))
    (tid : (s.lanes t).scalar.regs 0=BitVec.ofNat 32 t.val)
    (sb : sharedWords d≤s.shared.length) : SegmentRegular (config d) t (roundPrefix d k) s := by
  have inds := round_indices b hk t
  have tf : t.val<4294967296 := lt_trans t.isLt (width_fits b)
  have af : 2^(d-(k+1))<4294967296 := lt_of_le_of_lt (Nat.pow_le_pow_right (by decide) (Nat.sub_le _ _)) (width_fits b)
  have lf : 2*t.val+k*width d<4294967296 := inds.1
  have lp : 4*(2*t.val+k*width d)<18446744073709551616 := by omega
  have rp : 4*(2*t.val+k*width d+1)<18446744073709551616 := by omega
  by_cases active : t.val<2^(d-(k+1))
  · have ri : 2*t.val+k*width d+1<s.shared.length := lt_of_lt_of_le (inds.2.2 active) sb
    have li : 2*t.val+k*width d<s.shared.length := by omega
    simp only [Nat.two_mul] at lf lp rp li ri
    simp [roundPrefix,Dense.pointer,Dense.scalar,Dense.guarded,Dense.word,SegmentRegular,
      Reference.dispatch,scalarStep,Scalar.eval,Scalar.Instr.plain,Scalar.Guard.eval,
      Scalar.Operand32.eval,Scalar.Operand64.eval,Scalar.BinOp.eval,Scalar.Compare.eval,
      Scalar.update,setLane,arena,tid,←BitVec.ofNat_add,Nat.mod_eq_of_lt tf,
      Nat.mod_eq_of_lt af,active,four,succFour,Nat.mod_eq_of_lt lf,
      Scalar.addressIndex,Nat.mod_eq_of_lt lp,Nat.mod_eq_of_lt rp,li,ri]
  · simp [roundPrefix,Dense.pointer,Dense.scalar,Dense.guarded,Dense.word,SegmentRegular,
      Reference.dispatch,scalarStep,Scalar.eval,Scalar.Instr.plain,Scalar.Guard.eval,
      Scalar.Operand32.eval,Scalar.Operand64.eval,Scalar.BinOp.eval,Scalar.Compare.eval,
      Scalar.update,setLane,arena,tid,←BitVec.ofNat_add,Nat.mod_eq_of_lt tf,
      Nat.mod_eq_of_lt af,active]

theorem round_regular (b : Bounds d) (hk : k<d) (s : State (width d)) (t : Fin (width d))
    (tid : (s.lanes t).scalar.regs 0=BitVec.ofNat 32 t.val)
    (sb : sharedWords d≤s.shared.length) : SegmentRegular (config d) t (roundCode d k) s := by
  rw [roundCode,List.append_assoc,segmentRegular_append]
  refine ⟨round_prefix_regular b hk s t tid sb,?_⟩
  rw [segmentRegular_append]
  refine ⟨Scalar.MaximumSelect.regular _ _ _,?_⟩
  rw [Scalar.MaximumSelect.reference]
  have inds := round_indices b hk t
  have tf : t.val<4294967296 := lt_trans t.isLt (width_fits b)
  have af : 2^(d-(k+1))<4294967296 := lt_of_le_of_lt (Nat.pow_le_pow_right (by decide) (Nat.sub_le _ _)) (width_fits b)
  have lf : 2*t.val+k*width d<4294967296 := inds.1
  have nf : t.val+(k+1)*width d<4294967296 := by have := shared_fits b; dsimp [nextIndex] at inds; omega
  have lp : 4*(2*t.val+k*width d)<18446744073709551616 := by omega
  have rp : 4*(2*t.val+k*width d+1)<18446744073709551616 := by omega
  have np : 4*(t.val+(k+1)*width d)<18446744073709551616 := by omega
  have ni : t.val+(k+1)*width d<s.shared.length := by dsimp [nextIndex] at inds; omega
  by_cases active : t.val<2^(d-(k+1))
  · have ri : 2*t.val+k*width d+1<s.shared.length := lt_of_lt_of_le (inds.2.2 active) sb
    have li : 2*t.val+k*width d<s.shared.length := by omega
    simp only [Nat.two_mul] at lf lp rp li ri
    simp [roundPrefix,roundSuffix,Dense.pointer,Dense.scalar,Dense.guarded,Dense.word,
      segmentReference,SegmentRegular,Scalar.MaximumSelect.install,Scalar.MaximumSelect.finish,
      Reference.dispatch,scalarStep,Scalar.eval,Scalar.Instr.plain,Scalar.Guard.eval,
      Scalar.Operand32.eval,Scalar.Operand64.eval,Scalar.BinOp.eval,Scalar.Compare.eval,
      Scalar.update,setLane,arena,tid,←BitVec.ofNat_add,Nat.mod_eq_of_lt tf,
      Nat.mod_eq_of_lt af,active,four,succFour,Nat.mod_eq_of_lt lf,Nat.mod_eq_of_lt nf,
      Scalar.addressIndex,Nat.mod_eq_of_lt lp,Nat.mod_eq_of_lt rp,Nat.mod_eq_of_lt np,li,ri,ni]
  · simp [roundPrefix,roundSuffix,Dense.pointer,Dense.scalar,Dense.guarded,Dense.word,
      segmentReference,SegmentRegular,Scalar.MaximumSelect.install,Scalar.MaximumSelect.finish,
      Reference.dispatch,scalarStep,Scalar.eval,Scalar.Instr.plain,Scalar.Guard.eval,
      Scalar.Operand32.eval,Scalar.Operand64.eval,Scalar.BinOp.eval,Scalar.Compare.eval,
      Scalar.update,setLane,arena,tid,←BitVec.ofNat_add,Nat.mod_eq_of_lt tf,
      Nat.mod_eq_of_lt af,active]

theorem round_effect (b : Bounds d) (hk : k<d) (s : State (width d)) (t : Fin (width d))
    (tid : (s.lanes t).scalar.regs 0=BitVec.ofNat 32 t.val)
    (sb : sharedWords d≤s.shared.length) :
    (roundFinish d k s t).global=s.global ∧
    (roundFinish d k s t).shared=(if t.val<2^(d-(k+1)) then
      s.shared.set (nextIndex d k t) (Ptx.Binary32.Maximum.choose s.shared[leftIndex d k t]! s.shared[leftIndex d k t+1]!) else s.shared) ∧
    (roundFinish d k s t).site=s.site ∧
    ((roundFinish d k s t).lanes t).scalar.regs 0=(s.lanes t).scalar.regs 0 ∧
    (∀u,u≠t→(roundFinish d k s t).lanes u=s.lanes u) := by
  unfold roundFinish roundCode
  rw [List.append_assoc,segmentReference_append]
  simp only [segmentReference_append,Scalar.MaximumSelect.reference]
  have inds := round_indices b hk t
  have tf : t.val<4294967296 := lt_trans t.isLt (width_fits b)
  have af : 2^(d-(k+1))<4294967296 := lt_of_le_of_lt (Nat.pow_le_pow_right (by decide) (Nat.sub_le _ _)) (width_fits b)
  have lf : 2*t.val+k*width d<4294967296 := inds.1
  have nf : t.val+(k+1)*width d<4294967296 := by have := shared_fits b; dsimp [nextIndex] at inds; omega
  have lp : 4*(2*t.val+k*width d)<18446744073709551616 := by omega
  have rp : 4*(2*t.val+k*width d+1)<18446744073709551616 := by omega
  have np : 4*(t.val+(k+1)*width d)<18446744073709551616 := by omega
  have ni : t.val+(k+1)*width d<s.shared.length := by dsimp [nextIndex] at inds; omega
  by_cases active : t.val<2^(d-(k+1))
  · have ri : 2*t.val+k*width d+1<s.shared.length := lt_of_lt_of_le (inds.2.2 active) sb
    have li : 2*t.val+k*width d<s.shared.length := by omega
    simp only [Nat.two_mul] at lf lp rp li ri
    simp [roundPrefix,roundSuffix,Dense.pointer,Dense.scalar,Dense.guarded,Dense.word,
      segmentReference,Scalar.MaximumSelect.install,Scalar.MaximumSelect.finish,
      Reference.dispatch,scalarStep,Scalar.eval,Scalar.Instr.plain,Scalar.Guard.eval,
      Scalar.Operand32.eval,Scalar.Operand64.eval,Scalar.BinOp.eval,Scalar.Compare.eval,
      Scalar.update,setLane,arena,tid,←BitVec.ofNat_add,Nat.mod_eq_of_lt tf,
      Nat.mod_eq_of_lt af,active,Nat.two_mul,four,succFour,Nat.mod_eq_of_lt lf,Nat.mod_eq_of_lt nf,
      Scalar.addressIndex,Nat.mod_eq_of_lt lp,Nat.mod_eq_of_lt rp,Nat.mod_eq_of_lt np,li,ri,ni,
      leftIndex,nextIndex]
    intro u ne; simp [Function.update,ne]
  · simp [roundPrefix,roundSuffix,Dense.pointer,Dense.scalar,Dense.guarded,Dense.word,
      segmentReference,Scalar.MaximumSelect.install,Scalar.MaximumSelect.finish,
      Reference.dispatch,scalarStep,Scalar.eval,Scalar.Instr.plain,Scalar.Guard.eval,
      Scalar.Operand32.eval,Scalar.Operand64.eval,Scalar.BinOp.eval,Scalar.Compare.eval,
      Scalar.update,setLane,arena,tid,←BitVec.ofNat_add,Nat.mod_eq_of_lt tf,
      Nat.mod_eq_of_lt af,active]
    intro u ne; simp [Function.update,ne]


structure RoundInvariant (d : Nat) (start state : State (width d)) (k count : Nat) : Prop where
  global : state.global=start.global
  length : state.shared.length=start.shared.length
  old : ∀i,i<(k+1)*width d→state.shared[i]?=start.shared[i]?
  written : ∀t : Fin (width d),t.val<count→t.val<2^(d-(k+1))→
    state.shared[nextIndex d k t]?=some (nodeValue start.global (k+1) t.val)
  pc : ∀t : Fin (width d),(state.lanes t).scalar.pc=6+24*k+(if t.val<count then 23 else 0)
  live : ∀t,(state.lanes t).halted=false
  ids : ∀t,(state.lanes t).scalar.regs 0=(start.lanes t).scalar.regs 0
  barrier : state.barrier=start.barrier
  site : state.site=start.site

theorem round_reads (hk : k<d) (global : List Word) (start state : State (width d))
    (ready : Ready d global start k)
    (old : ∀i,i<(k+1)*width d→state.shared[i]?=start.shared[i]?)
    (t : Fin (width d)) (active : t.val<2^(d-(k+1))) :
    state.shared[leftIndex d k t]! =nodeValue global k (2*t.val) ∧
    state.shared[leftIndex d k t+1]! =nodeValue global k (2*t.val+1) := by
  have children := children_bound k d t.val hk active
  have w : 2^(d-k)≤width d := Nat.pow_le_pow_right (by decide) (Nat.sub_le _ _)
  have li : leftIndex d k t<(k+1)*width d := by dsimp [leftIndex]; rw [Nat.add_mul]; omega
  have ri : leftIndex d k t+1<(k+1)*width d := by dsimp [leftIndex]; rw [Nat.add_mul]; omega
  constructor
  · rw [List.getElem!_eq_getElem?_getD,old _ li]
    rw [show leftIndex d k t=k*width d+2*t.val by dsimp [leftIndex]; omega,ready.values _ children.1]
    rfl
  · rw [List.getElem!_eq_getElem?_getD,old _ ri]
    rw [show leftIndex d k t+1=k*width d+(2*t.val+1) by dsimp [leftIndex]; omega,ready.values _ children.2]
    rfl

theorem round_invariant_step (b : Bounds d) (hk : k<d) (global : List Word)
    (start state : State (width d)) (ready : Ready d global start k)
    (count : Nat) (hc : count<width d) (inv : RoundInvariant d start state k count) :
    RoundInvariant d start (roundFinish d k state ⟨count,hc⟩) k (count+1) := by
  let t : Fin (width d) := ⟨count,hc⟩
  have tid := (inv.ids t).trans (ready.ids t)
  have sb : sharedWords d≤state.shared.length := by rw [inv.length]; exact ready.extent
  have eff := round_effect b hk state t tid sb
  have frame := (segmentReference_concrete (round_regular b hk state t tid sb)).frame
  change ((roundFinish d k state t).lanes t).scalar.pc=_ ∧
    ((roundFinish d k state t).lanes t).halted=_ ∧ (roundFinish d k state t).barrier=_ at frame
  have pc0 : (state.lanes t).scalar.pc=6+24*k := by simp [inv.pc,t]
  refine ⟨eff.1.trans inv.global,?_,?_,?_,?_,?_,?_,frame.2.2.trans inv.barrier,eff.2.2.1.trans inv.site⟩
  · rw [eff.2.1]; split <;> simp [inv.length]
  · intro i hi
    rw [eff.2.1]
    split
    · rw [List.getElem?_set_ne (by dsimp [nextIndex]; omega)]; exact inv.old i hi
    · exact inv.old i hi
  · intro u hu active
    rw [eff.2.1]
    by_cases eq : u=t
    · subst u
      simp only [active,ite_true]
      have inside : nextIndex d k t<state.shared.length := lt_of_lt_of_le (round_indices b hk t).2.1 sb
      rw [List.getElem?_set_self inside]
      have reads := round_reads hk global start state ready inv.old t active
      simp [nodeValue,Ptx.Binary32.Maximum.Tree.nodeValue,reads.1,reads.2,ready.global]
    · have ne : nextIndex d k t≠nextIndex d k u := by
        intro h; apply eq; apply Fin.ext; dsimp [nextIndex] at h; omega
      split
      · rw [List.getElem?_set_ne ne]
        apply inv.written u (by have : u.val≠count := fun h => eq (Fin.ext h); omega) active
      · apply inv.written u (by have : u.val≠count := fun h => eq (Fin.ext h); omega) active
  · intro u
    by_cases eq : u=t
    · subst u; simpa [t,pc0] using frame.1
    · rw [eff.2.2.2.2 u eq,inv.pc]
      have ne : u.val≠count := fun h => eq (Fin.ext h)
      have same : u.val<count+1↔u.val<count := by omega
      simp [same]
  · intro u
    by_cases eq : u=t
    · subst u; exact frame.2.1.trans (inv.live t)
    · rw [eff.2.2.2.2 u eq]; exact inv.live u
  · intro u
    by_cases eq : u=t
    · subst u; exact eff.2.2.2.1.trans (inv.ids t)
    · rw [eff.2.2.2.2 u eq]; exact inv.ids u

theorem round_exists (b : Bounds d) (hk : k<d) (global : List Word) (start : State (width d))
    (ready : Ready d global start k) :
    ∃events final,ConcreteRuns (config d) (program d) start events final ∧
      Ready d global final (k+1) ∧ final.shared.length=start.shared.length := by
  have sweep : ∀count,count≤width d→∃events state,
      ConcreteRuns (config d) (program d) start events state ∧ RoundInvariant d start state k count := by
    intro count bound
    induction count with
    | zero =>
      refine ⟨[],start,.nil,rfl,rfl,?_,?_,?_,ready.live,?_,rfl,rfl⟩
      · intro i _; rfl
      · intro t ht; omega
      · intro t; simpa using ready.pc t
      · intro t; rfl
    | succ count ih =>
      obtain ⟨events,state,run,inv⟩ := ih (by omega)
      let t : Fin (width d) := ⟨count,by omega⟩
      have tid := (inv.ids t).trans (ready.ids t)
      have sb : sharedWords d≤state.shared.length := by rw [inv.length]; exact ready.extent
      have seg := segmentReference_concrete (round_regular b hk state t tid sb)
      have pc : (state.lanes t).scalar.pc=6+24*k := by simp [inv.pc,t]
      have tail := seg.compile (by rw [pc]; exact code_fetch (round_fetch d k hk)) (inv.live t)
        (by simp [inv.barrier,ready.barrier,Barrier.reset]) (eligible d)
      exact ⟨_,_,concrete_runs_append run tail,round_invariant_step b hk global start state ready count (by omega) inv⟩
  obtain ⟨events,state,run,inv⟩ := sweep (width d) (Nat.le_refl _)
  have pcs : ∀t,(state.lanes t).scalar.pc=6+24*k+23 := by intro t; simp [inv.pc,t.isLt]
  have fetch : (program d)[6+24*k+23]?=some (.sync 0) := by
    rw [round_fetch d k hk 23 (by simp)]
    simp [round]
  obtain ⟨barriers,brun⟩ := barrier_round_concrete (config d) state (program d) (6+24*k+23) (k+1)
    pcs inv.live (inv.barrier.trans ready.barrier) (inv.site.trans ready.site) fetch (eligible d)
  refine ⟨events++barriers,afterRound state (k+1),concrete_runs_append run brun,?_,inv.length⟩
  refine ⟨inv.global.trans ready.global,by change sharedWords d≤state.shared.length; rw [inv.length]; exact ready.extent,?_,inv.live,?_,rfl,rfl,?_⟩
  · intro t; simp [afterRound,pcs]; omega
  · intro t; exact (inv.ids t).trans (ready.ids t)
  · intro t ht
    have small : t<width d := lt_of_lt_of_le ht (Nat.pow_le_pow_right (by decide) (Nat.sub_le _ _))
    simpa [nextIndex,ready.global,afterRound,Nat.add_comm] using inv.written ⟨t,small⟩ small ht


def outputFinish (d : Nat) (s : State (width d)) (t : Fin (width d)) :=
  (segmentReference (config d) t (outputCode d) s).1

theorem output_regular (b : Bounds d) (s : State (width d)) (t : Fin (width d))
    (tid : (s.lanes t).scalar.regs 0=BitVec.ofNat 32 t.val)
    (gb : width d+1≤s.global.length) (sb : sharedWords d≤s.shared.length) :
    SegmentRegular (config d) t (outputCode d) s := by
  have tf : t.val<4294967296 := lt_trans t.isLt (width_fits b)
  have wf : width d<4294967296 := width_fits b
  have root := plane_bound d d 0 (by omega) (Nat.two_pow_pos _)
  have rf : d*width d<4294967296 := by have := shared_fits b; omega
  have rp : 4*(d*width d)<18446744073709551616 := by omega
  have wp : 4*width d<18446744073709551616 := by omega
  have ri : d*width d<s.shared.length := by omega
  have wi : width d<s.global.length := by omega
  by_cases leader : t.val=0
  · simp [outputCode,Dense.pointer,Dense.scalar,Dense.guarded,Dense.word,SegmentRegular,
      Reference.dispatch,scalarStep,Scalar.eval,Scalar.Instr.plain,Scalar.Guard.eval,
      Scalar.Operand32.eval,Scalar.Operand64.eval,Scalar.Compare.eval,Scalar.update,setLane,arena,
      tid,leader,Nat.mod_eq_of_lt wf,Nat.mod_eq_of_lt rf,←BitVec.ofNat_add,
      four,Scalar.addressIndex,Nat.mod_eq_of_lt rp,Nat.mod_eq_of_lt wp,ri,wi]
  · have nz : (BitVec.ofNat 32 t.val : Word)≠0#32 := by
      intro h
      have z := congrArg BitVec.toNat h
      simp only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt tf] at z
      change t.val=0 at z
      exact leader z
    simp [outputCode,Dense.pointer,Dense.scalar,Dense.guarded,Dense.word,SegmentRegular,
      Reference.dispatch,scalarStep,Scalar.eval,Scalar.Instr.plain,Scalar.Guard.eval,
      Scalar.Operand32.eval,Scalar.Operand64.eval,Scalar.Compare.eval,Scalar.update,setLane,arena,tid,nz]

theorem output_effect (b : Bounds d) (s : State (width d)) (t : Fin (width d))
    (tid : (s.lanes t).scalar.regs 0=BitVec.ofNat 32 t.val)
    (gb : width d+1≤s.global.length) (sb : sharedWords d≤s.shared.length) :
    (outputFinish d s t).global=(if t.val=0 then s.global.set (width d) s.shared[d*width d]! else s.global) ∧
    (outputFinish d s t).shared=s.shared ∧
    (outputFinish d s t).site=s.site ∧
    ((outputFinish d s t).lanes t).scalar.regs 0=(s.lanes t).scalar.regs 0 ∧
    (∀u,u≠t→(outputFinish d s t).lanes u=s.lanes u) := by
  have tf : t.val<4294967296 := lt_trans t.isLt (width_fits b)
  have wf : width d<4294967296 := width_fits b
  have root := plane_bound d d 0 (by omega) (Nat.two_pow_pos _)
  have rf : d*width d<4294967296 := by have := shared_fits b; omega
  have rp : 4*(d*width d)<18446744073709551616 := by omega
  have wp : 4*width d<18446744073709551616 := by omega
  have ri : d*width d<s.shared.length := by omega
  have wi : width d<s.global.length := by omega
  by_cases leader : t.val=0
  · simp [outputFinish,outputCode,Dense.pointer,Dense.scalar,Dense.guarded,Dense.word,segmentReference,
      Reference.dispatch,scalarStep,Scalar.eval,Scalar.Instr.plain,Scalar.Guard.eval,
      Scalar.Operand32.eval,Scalar.Operand64.eval,Scalar.Compare.eval,Scalar.update,setLane,arena,
      tid,leader,Nat.mod_eq_of_lt wf,Nat.mod_eq_of_lt rf,←BitVec.ofNat_add,
      four,Scalar.addressIndex,Nat.mod_eq_of_lt rp,Nat.mod_eq_of_lt wp,ri,wi]
    intro u ne; simp [Function.update,ne]
  · have nz : (BitVec.ofNat 32 t.val : Word)≠0#32 := by
      intro h
      have z := congrArg BitVec.toNat h
      simp only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt tf] at z
      change t.val=0 at z
      exact leader z
    simp [outputFinish,outputCode,Dense.pointer,Dense.scalar,Dense.guarded,Dense.word,segmentReference,
      Reference.dispatch,scalarStep,Scalar.eval,Scalar.Instr.plain,Scalar.Guard.eval,
      Scalar.Operand32.eval,Scalar.Operand64.eval,Scalar.Compare.eval,Scalar.update,setLane,arena,tid,nz,leader]
    intro u ne; simp [Function.update,ne]

structure OutputInvariant (d : Nat) (start state : State (width d)) (count : Nat) : Prop where
  global : state.global=if count=0 then start.global else start.global.set (width d) start.shared[d*width d]!
  shared : state.shared=start.shared
  pc : ∀t : Fin (width d),(state.lanes t).scalar.pc=6+24*d+(if t.val<count then 11 else 0)
  live : ∀t,(state.lanes t).halted=false
  ids : ∀t,(state.lanes t).scalar.regs 0=(start.lanes t).scalar.regs 0
  barrier : state.barrier=start.barrier
  site : state.site=start.site

theorem output_invariant_step (b : Bounds d) (global : List Word) (start state : State (width d))
    (ready : Ready d global start d) (gb : width d+1≤global.length)
    (count : Nat) (hc : count<width d) (inv : OutputInvariant d start state count) :
    OutputInvariant d start (outputFinish d state ⟨count,hc⟩) (count+1) := by
  let t : Fin (width d) := ⟨count,hc⟩
  have tid := (inv.ids t).trans (ready.ids t)
  have gl : state.global.length=global.length := by rw [inv.global]; split <;> simp [ready.global]
  have g : width d+1≤state.global.length := by rw [gl]; exact gb
  have sh : sharedWords d≤state.shared.length := by rw [inv.shared]; exact ready.extent
  have eff := output_effect b state t tid g sh
  have frame := (segmentReference_concrete (output_regular b state t tid g sh)).frame
  change ((outputFinish d state t).lanes t).scalar.pc=_ ∧
    ((outputFinish d state t).lanes t).halted=_ ∧ (outputFinish d state t).barrier=_ at frame
  have pc0 : (state.lanes t).scalar.pc=6+24*d := by simp [inv.pc,t]
  refine ⟨?_,eff.2.1.trans inv.shared,?_,?_,?_,frame.2.2.trans inv.barrier,eff.2.2.1.trans inv.site⟩
  · rw [eff.1,inv.global,inv.shared]
    by_cases hz : count=0 <;> simp [t,hz]
  · intro u
    by_cases eq : u=t
    · subst u; simpa [t,pc0] using frame.1
    · rw [eff.2.2.2.2 u eq,inv.pc]
      have ne : u.val≠count := fun h => eq (Fin.ext h)
      have same : u.val<count+1↔u.val<count := by omega
      simp [same]
  · intro u
    by_cases eq : u=t
    · subst u; exact frame.2.1.trans (inv.live t)
    · rw [eff.2.2.2.2 u eq]; exact inv.live u
  · intro u
    by_cases eq : u=t
    · subst u; exact eff.2.2.2.1.trans (inv.ids t)
    · rw [eff.2.2.2.2 u eq]; exact inv.ids u

theorem exit_sweep_memory {cfg : Config n} {prog : List Instr} {start : State n}
    (pc generation : Nat) (pcs : ∀t,(start.lanes t).scalar.pc=pc)
    (live : ∀t,(start.lanes t).halted=false) (barrier : start.barrier=Barrier.reset generation)
    (fetch : prog[pc]?=some .exit) (eligible : Mixed.Eligible cfg.target) :
    ∃events final,ConcreteRuns cfg prog start events final ∧ final.global=start.global ∧
      final.shared=start.shared ∧ ∀t,(final.lanes t).halted=true := by
  have sweep : ∀count,count≤n→∃events state,ConcreteRuns cfg prog start events state ∧
      state.global=start.global ∧ state.shared=start.shared ∧
      (∀t,(state.lanes t).scalar.pc=pc) ∧
      (∀t : Fin n,(state.lanes t).halted=decide (t.val<count)) ∧ state.barrier=Barrier.reset generation := by
    intro count bound
    induction count with
    | zero => exact ⟨[],start,.nil,rfl,rfl,pcs,by simpa using live,barrier⟩
    | succ count ih =>
      obtain ⟨events,state,run,global,shared,positions,halted,reset⟩ := ih (by omega)
      let t : Fin n := ⟨count,by omega⟩
      let out := Reference.dispatch cfg t .exit state
      have step : Step cfg prog none t state out := by
        refine ⟨eligible,?_⟩
        have live : (state.lanes t).halted=false := by simp [halted,t]
        simp only [live,reset,Barrier.reset,Bool.false_eq_true,ite_false,positions,fetch]
        exact Dispatch.exit
      have one := ConcreteRuns.cons step ConcreteRuns.nil
      refine ⟨events++out.events,out.state,concrete_runs_append run (by simpa using one),global,shared,?_,?_,reset⟩
      · intro u
        by_cases same : u=t
        · subst u; simpa [out,Reference.dispatch,setLane] using positions t
        · simpa [out,Reference.dispatch,setLane,Function.update,same] using positions u
      · intro u
        by_cases same : u=t
        · subst u; simp [out,Reference.dispatch,setLane,t]
        · have ne : u.val≠count := fun h => same (Fin.ext h)
          have eq : u.val<count+1↔u.val<count := by omega
          simp [out,Reference.dispatch,setLane,Function.update,same,halted,eq]
  obtain ⟨events,final,run,global,shared,_,halted,_⟩ := sweep n (Nat.le_refl _)
  exact ⟨events,final,run,global,shared,fun t=>by simp [halted,t.isLt]⟩

theorem output_exists (b : Bounds d) (global : List Word) (start : State (width d))
    (ready : Ready d global start d) (gb : width d+1≤global.length) :
    ∃events final,ConcreteRuns (config d) (program d) start events final ∧
      final.global=global.set (width d) (nodeValue global d 0) ∧ final.shared=start.shared ∧
      (∀t,(final.lanes t).halted=true) := by
  have sweep : ∀count,count≤width d→∃events state,
      ConcreteRuns (config d) (program d) start events state ∧ OutputInvariant d start state count := by
    intro count bound
    induction count with
    | zero =>
      refine ⟨[],start,.nil,by simp,rfl,?_,ready.live,?_,rfl,rfl⟩
      · intro t; simpa using ready.pc t
      · intro t; rfl
    | succ count ih =>
      obtain ⟨events,state,run,inv⟩ := ih (by omega)
      let t : Fin (width d) := ⟨count,by omega⟩
      have tid := (inv.ids t).trans (ready.ids t)
      have gl : state.global.length=global.length := by rw [inv.global]; split <;> simp [ready.global]
      have g : width d+1≤state.global.length := by rw [gl]; exact gb
      have sh : sharedWords d≤state.shared.length := by rw [inv.shared]; exact ready.extent
      have seg := segmentReference_concrete (output_regular b state t tid g sh)
      have pc : (state.lanes t).scalar.pc=6+24*d := by simp [inv.pc,t]
      have tail := seg.compile (by rw [pc]; exact code_fetch (output_fetch d)) (inv.live t)
        (by simp [inv.barrier,ready.barrier,Barrier.reset]) (eligible d)
      exact ⟨_,_,concrete_runs_append run tail,output_invariant_step b global start state ready gb count (by omega) inv⟩
  obtain ⟨events,state,run,inv⟩ := sweep (width d) (Nat.le_refl _)
  have pcs : ∀t,(state.lanes t).scalar.pc=6+24*d+11 := by intro t; simp [inv.pc,t.isLt]
  have fetch : (program d)[6+24*d+11]?=some .exit := by
    rw [output_fetch d 11 (by simp)]
    simp [output]
  obtain ⟨exits,final,erun,fg,fs,halted⟩ := exit_sweep_memory (pc:=6+24*d+11) (generation:=d+1) pcs inv.live
    (inv.barrier.trans ready.barrier) fetch (eligible d)
  have root : start.shared[d*width d]! =nodeValue global d 0 := by
    rw [List.getElem!_eq_getElem?_getD]
    have v := ready.values 0 (by simp)
    have h : start.shared[d*width d]?=some (nodeValue global d 0) := by simpa using v
    rw [h]
    rfl
  refine ⟨events++exits,final,concrete_runs_append run erun,?_,fs.trans inv.shared,halted⟩
  rw [fg,inv.global,ite_eq_right (Nat.ne_of_gt (Nat.two_pow_pos _)),ready.global,root]


/-- A complete concrete schedule executes every actual instruction and exits.
The shared scratch may initially contain arbitrary words. -/
theorem selected_complete (b : Bounds d) (global shared : List Word) (seeds : Fin (width d)→Scalar.State)
    (gb : width d+1≤global.length) (sb : sharedWords d≤shared.length) :
    ∃events final,ConcreteRuns (config d) (program d) (initial d global shared seeds) events final ∧
      final.global=global.set (width d) (nodeValue global d 0) ∧
      (∀t,(final.lanes t).halted=true) ∧ final.shared.length=shared.length ∧
      ∀event∈events,AccessSafe (initial d global shared seeds) event := by
  obtain ⟨first,start,published,ready,length⟩ := publish_exists b global shared seeds gb sb
  have rounds : ∀k,k≤d→∃events state,ConcreteRuns (config d) (program d) start events state ∧
      Ready d global state k ∧ state.shared.length=start.shared.length := by
    intro k bound
    induction k with
    | zero => exact ⟨[],start,.nil,ready,rfl⟩
    | succ k ih =>
      obtain ⟨events,state,run,ready,len⟩ := ih (by omega)
      obtain ⟨next,final,tail,after,eq⟩ := round_exists b (by omega) global state ready
      exact ⟨events++next,final,concrete_runs_append run tail,after,eq.trans len⟩
  obtain ⟨middle,state,reduced,root,len⟩ := rounds d (Nat.le_refl _)
  obtain ⟨last,final,stored,output,frame,done⟩ := output_exists b global state root gb
  have run := concrete_runs_append (concrete_runs_append published reduced) stored
  exact ⟨(first++middle)++last,final,run,output,done,by rw [frame,len,length],runs_access_safe run.toRuns⟩

/-- The same complete trace has a proved admitted and grounded memory graph.
This is an existence theorem; universal candidate correctness is separate. -/
theorem selected_admitted (b : Bounds d) (global shared : List Word) (seeds : Fin (width d)→Scalar.State)
    (gb : width d+1≤global.length) (sb : sharedWords d≤shared.length) :
    ∃events final,∃run : ConcreteRuns (config d) (program d) (initial d global shared seeds) events final,
      ∃source co,
      Graph.Ordered.Valid (Memory.graph (program d) global shared events source co)
        (Memory.runOrder run.toRuns (show (initial d global shared seeds).barrier=Barrier.reset 0 from rfl) source co).cross ∧
      (∀i,¬Path (SharedReduction.Machine.Memory.grounding
        (Memory.graph (program d) global shared events source co)
        (Memory.runOrder run.toRuns (show (initial d global shared seeds).barrier=Barrier.reset 0 from rfl) source co).cross) i i) ∧
      final.global=global.set (width d) (nodeValue global d 0) ∧
      (∀t,(final.lanes t).halted=true) ∧ final.shared.length=shared.length ∧
      ∀event∈events,AccessSafe (initial d global shared seeds) event := by
  obtain ⟨events,final,run,value,done,extent,safe⟩ := selected_complete b global shared seeds gb sb
  obtain ⟨source,co,valid,grounded⟩ := Memory.Chronology.concrete_admitted run
    (show (initial d global shared seeds).barrier=Barrier.reset 0 from rfl)
  exact ⟨events,final,run,source,co,valid,grounded,value,done,extent,safe⟩

end Ptx.Scalar.Parallel.Maximum

import PoissonPTX.DotSetupRegisters
import PoissonPTX.DotSuffixOrder

namespace PtxTorchLean.Poisson.PTX.Concurrent.Dot

def treeLimit (pc : Nat) : Nat :=
  if 24≤pc ∧ pc<96 ∧ 2≤(pc-24)%9 ∧ (pc-24)%9≤7 then 256 / 2^((pc-24)/9+1) else 256

def treeGuard (pc : Nat) : Option Nat :=
  if 24≤pc ∧ pc<96 ∧ (pc-24)%9=1 then some (256 / 2^((pc-24)/9+1)) else none

def TreeControl (thread : Fin 256) (s : Flow.State) : Prop :=
  thread.val<treeLimit s.core.pc ∧ ∀ count, treeGuard s.core.pc=some count →
    s.predicates 0=decide (count≤thread.val)

theorem tree_control_outside (early : s.core.pc≤20 ∨ 96≤s.core.pc) : TreeControl thread s := by
  have outside : ¬(24≤s.core.pc ∧ s.core.pc<96) := by omega
  simp only [TreeControl,treeLimit,treeGuard]
  have noLimit : ¬(24≤s.core.pc ∧ s.core.pc<96 ∧ 2≤(s.core.pc-24)%9 ∧ (s.core.pc-24)%9≤7) := by tauto
  have noGuard : ¬(24≤s.core.pc ∧ s.core.pc<96 ∧ (s.core.pc-24)%9=1) := by tauto
  simp [noLimit,noGuard,thread.isLt]

theorem checked_tree_control : ∀ slot : Fin 76,
    (match Reduction.Native.code[slot.val]? with
    | some (.data _) => decide (treeLimit (20+slot.val)≤treeLimit (21+slot.val) ∧ treeGuard (21+slot.val)=none)
    | some (.compare count) => decide (treeLimit (20+slot.val)≤treeLimit (21+slot.val) ∧
        treeGuard (21+slot.val)=some count ∧ count<2^32)
    | some (.branch target) => decide (∃ count : Fin 257, treeGuard (20+slot.val)=some count.val ∧
        count.val≤treeLimit (21+slot.val) ∧ treeGuard (21+slot.val)=none ∧
        256≤treeLimit (20+target) ∧ treeGuard (20+target)=none)
    | some (.sync _) => decide (256≤treeLimit (21+slot.val) ∧ treeGuard (21+slot.val)=none)
    | none => true)=true := by decide +kernel

/-- The private predicate is derived from the fetched comparison. The active
lane bound therefore follows from the actual branch, regardless of scheduling. -/
theorem tree_control_native {thread : Fin 256}
    (fetch : Reduction.Native.code[slot]?=some native)
    (ordinary : treeInstruction native=.flow i)
    (pc : s.core.pc=20+slot)
    (actual : Flow.Observed.Eval ctx i s t access index)
    (lane : s.core.regs 14=ctx.lane.setWidth 64) (laneMap : ctx.lane.toNat=thread.val)
    (ready : TreeControl thread s) : TreeControl thread t := by
  have bound := (List.getElem?_eq_some_iff.mp fetch).1
  rw [Reduction.Native.length] at bound
  have checked := checked_tree_control ⟨slot,bound⟩
  rw [fetch] at checked
  cases native <;> cases ordinary
  · simp only [decide_eq_true_eq] at checked
    cases actual with
    | data step =>
      have counter := Indexed.Candidate.data_pc step
      rw [pc] at counter
      have counter := counter.trans (show 20+slot+1=21+slot by omega)
      refine ⟨?_,?_⟩
      · rw [counter]; exact lt_of_lt_of_le (pc ▸ ready.1) checked.1
      · intro count found; rw [counter,checked.2] at found; cases found
    | simple ordinary => exact False.elim (ordinary _ rfl)
  · rename_i count
    simp only [decide_eq_true_eq] at checked
    cases actual
    have laneValue : (s.core.regs 14).toNat=thread.val := by simp [lane,BitVec.toNat_setWidth,laneMap,Nat.mod_eq_of_lt (show thread.val<18446744073709551616 by have := thread.isLt; omega)]
    have comparison := NativeGuard.compare_value laneValue (by decide +kernel) checked.2.2
    constructor
    · change thread.val<treeLimit (s.core.pc+1)
      rw [pc,show 20+slot+1=21+slot by omega]
      exact lt_of_lt_of_le (pc ▸ ready.1) checked.1
    · intro other found
      change treeGuard (s.core.pc+1)=some other at found
      rw [pc,show 20+slot+1=21+slot by omega,checked.2.1] at found
      cases found
      simpa [Flow.simple,Flow.next,Operand.eval] using comparison
  · rename_i target
    simp only [decide_eq_true_eq] at checked
    obtain ⟨count,tag,fallBound,fallGuard,jumpBound,jumpGuard⟩ := checked
    have flag := ready.2 count.val (pc ▸ tag)
    cases actual
    change TreeControl thread (if s.predicates 0=true then Flow.goto s (20+target) else Flow.next s)
    split
    · exact ⟨lt_of_lt_of_le thread.isLt jumpBound,by intro c h; change treeGuard (20+target)=some c at h; rw [jumpGuard] at h; cases h⟩
    · rename_i notTaken
      have active : thread.val<count.val := by rw [flag] at notTaken; simp only [decide_eq_true_eq] at notTaken; omega
      refine ⟨?_,?_⟩
      · change thread.val<treeLimit (s.core.pc+1)
        rw [pc,show 20+slot+1=21+slot by omega]
        exact lt_of_lt_of_le active fallBound
      · intro c h
        change treeGuard (s.core.pc+1)=some c at h
        rw [pc,show 20+slot+1=21+slot by omega,fallGuard] at h
        cases h

theorem tree_control_flow {thread : Fin 256}
    (fetch : (program count left right output scratch)[s.core.pc]?=some (.flow i))
    (actual : Flow.Observed.Eval ctx i s t access index)
    (setup : SetupRegisters ctx scratch s) (laneMap : ctx.lane.toNat=thread.val)
    (ready : TreeControl thread s) : TreeControl thread t := by
  by_cases input : s.core.pc<20
  · rw [input_fetch input] at fetch
    obtain ⟨op,found,equal⟩ := Option.map_eq_some_iff.mp fetch
    cases equal
    apply tree_control_outside (Or.inl (NativeFlow.eval_upper actual input (input_syntax (List.mem_of_getElem? found)).1))
  · by_cases inside : s.core.pc<96
    · have position : s.core.pc=20+(s.core.pc-20) := by omega
      rw [position,tree_fetch (by omega)] at fetch
      obtain ⟨op,found,equal⟩ := Option.map_eq_some_iff.mp fetch
      exact tree_control_native found equal position actual (setup.2 (by omega)) laneMap ready
    · apply tree_control_outside (Or.inr (NativeFlow.eval_lower actual (by omega) ?_))
      have position : s.core.pc=96+(s.core.pc-96) := by omega
      rw [position,tail_fetch] at fetch
      obtain ⟨op,found,equal⟩ := Option.map_eq_some_iff.mp fetch
      cases equal
      have member := List.mem_of_getElem? found
      simp only [tail,List.mem_cons,List.not_mem_nil,or_false] at member
      rcases member with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> trivial

theorem tree_control_sync {thread : Fin 256}
    (fetch : (program count left right output scratch)[s.core.pc]?=some (.sync resource)) :
    TreeControl thread (Flow.next s) := by
  have lower : 20≤s.core.pc := by
    by_contra h
    exact no_early_sync (by omega) fetch
  have upper : s.core.pc<96 := by
    by_contra h
    have position : s.core.pc=96+(s.core.pc-96) := by omega
    rw [position,tail_fetch] at fetch
    cases (tail output)[s.core.pc-96]? <;> simp at fetch
  have position : s.core.pc=20+(s.core.pc-20) := by omega
  rw [position,tree_fetch (by omega)] at fetch
  obtain ⟨op,found,equal⟩ := Option.map_eq_some_iff.mp fetch
  have checked := checked_tree_control ⟨s.core.pc-20,by omega⟩
  rw [found] at checked
  cases op <;> cases equal
  simp only [decide_eq_true_eq] at checked
  have nextPC : (Flow.next s).core.pc=21+(s.core.pc-20) := by change s.core.pc+1=_; omega
  exact ⟨by rw [nextPC]; exact lt_of_lt_of_le thread.isLt checked.1,
    by intro c h; rw [nextPC,checked.2] at h; cases h⟩

theorem tree_control {cfg : Config 256} {ctx : Fin 256 → Kernel.Context}
    (run : NativeFlow.Runs cfg ctx (program count left right output scratch) start events indices final)
    (aligned : Aligned start.core) (entry : ∀ thread, (start.core.lanes thread).pc=0)
    (laneMap : ∀ thread, (ctx thread).lane.toNat=thread.val) :
    ∀ owner, TreeControl owner (NativeFlow.lane final owner) := by
  have inv : ∀ owner, SetupRegisters (ctx owner) scratch (NativeFlow.lane final owner) ∧
      TreeControl owner (NativeFlow.lane final owner) := by
    apply NativeFlow.runs_lanes (P:=fun owner s => SetupRegisters (ctx owner) scratch s ∧ TreeControl owner s) run aligned
      (fun owner => ⟨by simp [SetupRegisters,NativeFlow.lane,entry],
        tree_control_outside (Or.inl (by simp [NativeFlow.lane,entry]))⟩)
    · intro owner i before after access index ready fetch actual
      exact ⟨setup_registers_flow fetch actual ready.1,tree_control_flow fetch actual ready.1 (laneMap owner) ready.2⟩
    · intro owner before resource ready fetch
      refine ⟨⟨NativeFlow.initialized_sync ready.1.1 fetch (no_early_sync (by decide)),
        NativeFlow.initialized_sync ready.1.2 fetch (no_early_sync (by decide))⟩,tree_control_sync fetch⟩
  exact fun owner => (inv owner).2

end PtxTorchLean.Poisson.PTX.Concurrent.Dot

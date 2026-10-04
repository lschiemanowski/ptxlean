import PoissonPTX.DotReturns
import PoissonPTX.DotSetupRegisters
import PoissonPTX.DotOutputExists

namespace PtxTorchLean.Poisson.PTX.Concurrent.Dot

def ZeroControl (s : Flow.State) : Prop :=
  (s.core.pc=97 → s.predicates 0=false) ∧ (s.halted=true → 102<s.core.pc)

theorem zero_flow (fetch : (program count left right output scratch)[s.core.pc]?=some (.flow i))
    (actual : Flow.Observed.Eval ctx i s t access index)
    (setup : SetupRegisters ctx scratch s) (laneZero : ctx.lane=0) (ready : ZeroControl s) : ZeroControl t := by
  by_cases early : s.core.pc<96
  · have targets := barrier_stops (count:=count) (left:=left) (right:=right) (output:=output) (scratch:=scratch)
      8 s.core.pc i fetch (by change s.core.pc≤95; omega)
    have bound := NativeFlow.eval_upper actual early
      (show NativeFlow.targets (·≤96) i by cases i <;> simp_all [NativeFlow.targets,barrierSite] <;> omega)
    have live : s.halted=false := by
      cases flag : s.halted
      · rfl
      · have := ready.2 flag; omega
    have after := NativeFlow.eval_live actual (continues_through_tree (by omega) fetch) live
    exact ⟨by omega,by simp [after]⟩
  · have length : s.core.pc<104 := by
      have bound := (List.getElem?_eq_some_iff.mp fetch).1
      simpa only [Dot.length] using bound
    rw [show s.core.pc=96+(s.core.pc-96) by omega,tail_fetch] at fetch
    interval_cases pcEq : s.core.pc
    all_goals simp only [tail] at fetch
    all_goals cases fetch
    · have reg : s.core.regs 14=0 := by simpa [laneZero] using setup.2 (by omega)
      cases actual
      simp [ZeroControl,Flow.simple,Flow.next,advance,Operand.eval,reg,Flow.Compare.apply,Kernel.u32,pcEq]
      cases flag : s.halted
      · rfl
      · have := ready.2 flag; omega
    · have pred := ready.1 pcEq
      cases actual
      simpa [Flow.simple,pred,Flow.next,ZeroControl,advance,pcEq] using ready.2
    · cases actual with
      | data step =>
        have pc := Indexed.Candidate.data_pc step
        exact ⟨by simp_all,by intro h; have := ready.2 h; omega⟩
      | simple ordinary => exact False.elim (ordinary _ rfl)
    · cases actual with
      | data step =>
        have pc := Indexed.Candidate.data_pc step
        exact ⟨by simp_all,by intro h; have := ready.2 h; omega⟩
      | simple ordinary => exact False.elim (ordinary _ rfl)
    · cases actual with
      | data step =>
        have pc := Indexed.Candidate.data_pc step
        exact ⟨by simp_all,by intro h; have := ready.2 h; omega⟩
      | simple ordinary => exact False.elim (ordinary _ rfl)
    · cases actual with
      | data step =>
        have pc := Indexed.Candidate.data_pc step
        exact ⟨by simp_all,by intro h; have := ready.2 h; omega⟩
      | simple ordinary => exact False.elim (ordinary _ rfl)
    · cases actual with
      | data step =>
        have pc := Indexed.Candidate.data_pc step
        simp [ZeroControl,pc,pcEq]
      | simple ordinary => exact False.elim (ordinary _ rfl)
    · cases actual
      simp [ZeroControl,Flow.simple,Flow.halt,Flow.next,advance,pcEq]

theorem zero_sync (fetch : (program count left right output scratch)[s.core.pc]?=some (.sync resource))
    (ready : ZeroControl s) : ZeroControl (Flow.next s) := by
  have upper : s.core.pc<96 := by
    by_contra h
    have position : s.core.pc=96+(s.core.pc-96) := by omega
    rw [position,tail_fetch] at fetch
    cases (tail output)[s.core.pc-96]? <;> simp at fetch
  refine ⟨?_,?_⟩
  · change s.core.pc+1=97 → s.predicates 0=false
    omega
  · intro halted
    have bound := ready.2 halted
    change 102<s.core.pc+1
    omega

theorem zero_returned_store {start : NativeFlow.State 256}
    (run : NativeFlow.Runs cfg ctx (program count left right output scratch) start events indices final)
    (reset : start.core.barrier=Ptx.Barrier.reset generation)
    (entry : ∀ owner, (start.core.lanes owner).pc=0) (live : start.halted 0=false)
    (laneZero : (ctx 0).lane=0) (returned : final.halted 0=true) :
    ∃ access, Event.data 0 access∈events ∧ access.data.pc=102 ∧ access.data.store=true ∧ access.space=.global := by
  have aligned : Aligned start.core := by intro t h; simp [reset,Ptx.Barrier.reset] at h
  have inv : ∀ owner, SetupRegisters (ctx owner) scratch (NativeFlow.lane final owner) ∧
      (owner=0 → ZeroControl (NativeFlow.lane final owner)) := by
    apply NativeFlow.runs_lanes (P:=fun owner s => SetupRegisters (ctx owner) scratch s ∧ (owner=0 → ZeroControl s)) run aligned
    · intro owner
      refine ⟨by simp [SetupRegisters,NativeFlow.lane,entry],?_⟩
      intro same; subst owner
      simp [ZeroControl,NativeFlow.lane,entry,live]
    · intro owner i before after access index ready fetch actual
      refine ⟨setup_registers_flow fetch actual ready.1,?_⟩
      intro same; subst owner
      exact zero_flow fetch actual ready.1 laneZero (ready.2 rfl)
    · intro owner before resource ready fetch
      refine ⟨⟨NativeFlow.initialized_sync ready.1.1 fetch (no_early_sync (by decide)),
        NativeFlow.initialized_sync ready.1.2 fetch (no_early_sync (by decide))⟩,?_⟩
      intro same; exact zero_sync fetch (ready.2 same)
  apply NativeFlow.crossed_store run aligned (sp:=.global) (addr:=.reg 2) (src:=.reg 8)
  · rw [show 102=96+6 by rfl,tail_fetch]; rfl
  · intro before earlier earlierIndices prior; exact protects_output
  · rw [entry]; decide
  · exact (inv 0).2 rfl |>.2 returned

end PtxTorchLean.Poisson.PTX.Concurrent.Dot

import PoissonPTX.NativeGuardExists
import PoissonPTX.ReductionNativeCode
import PoissonPTX.ReductionComplete
import PoissonPTX.ReductionSafety

namespace PtxTorchLean.Poisson.PTX.Concurrent.Reduction.Native
open Control Visibility.Repeated

variable {cfg : Config 256} {s t : NativeGuard.State 256}

/-- Numerical correctness with separately scheduled native comparison and
branch instructions. The theorem uses actual predicate state, rather than an
assumption that each branch took the desired path. -/
theorem correct (run : NativeGuard.Runs cfg program s events t)
    (clean : ∀ u, s.pending u=false)
    (reset : s.core.barrier=Ptx.Barrier.reset generation)
    (entry : ∀ u, (s.core.lanes u).pc=0)
    (baseReg : ∀ u, ((s.core.lanes u).regs 3).toNat=base)
    (laneReg : ∀ u, ((s.core.lanes u).regs 14).toNat=u.val)
    (inputs : ∀ u, decode ((s.core.lanes u).regs 8)=input u.val)
    (noWrap : base+2048≤2^64)
    (compatible : Visibility.Compatible initialMemory events source)
    (ordered : OrderedSources events source)
    (done : ∀ u, (t.core.lanes u).pc=program.length) :
    ∃ (w : Nat) (access : Access), events[w]?=some (.data 0 access) ∧
      access.data.pc=66 ∧ access.data.store=true ∧ access.space=.shared ∧
      access.data.address=base ∧ decode access.data.value=Binary64.reduce256 input := by
  have ready : NativeGuard.Ready program s := ⟨by simp [clean],laneReg⟩
  have projection := (NativeGuard.project run ready frames.2 counts (by decide +kernel)).1
  exact Numeric.completed_result projection reset entry baseReg laneReg inputs noWrap compatible ordered done

/-- The old complete admitted witness lifts to a complete native guard run.
Its event history, byte choices and coherence witness are unchanged. -/
theorem exists_correct {input : Nat → Word} (s : Concurrent.State 256)
    (ready : Witness256.ReadyAt base 0 generation s) (aligned : base%8=0)
    (inputs : ∀ u, (s.lanes u).regs 8=input u.val) (initialMemory : Space → Memory)
    (flags : Fin 256 → Bool) :
    ∃ final flags' events source,
      NativeGuard.Runs cfg program (NativeGuard.start s flags) events (NativeGuard.start final flags') ∧
      (∀ u, (final.lanes u).pc=program.length) ∧
      Visibility.Compatible initialMemory events source ∧ OrderedSources events source ∧
      ∃ (w : Nat) (a : Access), events[w]?=some (.data 0 a) ∧
        a.data.pc=66 ∧ a.data.store=true ∧ a.space=.shared ∧ a.data.address=base ∧
        decode a.data.value=Binary64.reduce256 (fun i => decode (input i)) := by
  obtain ⟨final,events,source,run,done,compatible,ordered,result⟩ :=
    Witness256.exists_correct s ready aligned inputs initialMemory (cfg:=cfg)
  obtain ⟨flags',native⟩ := NativeGuard.lift run (fun u => (ready.1 u).2.1)
    frames.2 counts (by decide +kernel) flags
  exact ⟨final,flags',events,source,native,done,compatible,ordered,result⟩

theorem safe (run : NativeGuard.Runs cfg program s events t)
    (clean : ∀ u, s.pending u=false) (aligned : Aligned s.core)
    (entry : ∀ u, (s.core.lanes u).pc=0)
    (baseReg : ∀ u, ((s.core.lanes u).regs 3).toNat=base)
    (laneReg : ∀ u, ((s.core.lanes u).regs 14).toNat=u.val)
    (baseAligned : base%8=0) (noWrap : base+2048≤2^64)
    (member : Event.data thread access∈events) :
    access.space=.shared ∧ Valid64 base 2048 access.data.address := by
  have ready : NativeGuard.Ready program s := ⟨by simp [clean],laneReg⟩
  exact memory_safety (NativeGuard.project run ready frames.2 counts (by decide +kernel)).1
    aligned entry baseReg laneReg baseAligned noWrap member

end PtxTorchLean.Poisson.PTX.Concurrent.Reduction.Native

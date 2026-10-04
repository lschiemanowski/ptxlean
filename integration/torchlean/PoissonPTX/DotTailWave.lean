import PoissonPTX.DotTailLane

namespace PtxTorchLean.Poisson.PTX.Concurrent.Dot.Witness
open Reduction.Control.Witness256

def TailEvent (word : Word) : Event 256 → Prop
  | .barrier _ => False
  | .data t a => t=0 ∧ a.data.value=word ∧
      ((a.space=.shared ∧ a.data.store=false ∧ a.data.pc=98) ∨
       (a.space=.global ∧ a.data.store=true ∧ a.data.pc=102))

theorem tail_wave (start : NativeFlow.State 256) (ready : ReadyAt base 96 generation start)
    (aligned : base%8=0)
    (outputs : ∀ t, Valid64 (start.core.lanes t).globalStart (start.core.lanes t).globalBytes
      ((start.core.lanes t).regs 0+output).toNat) :
    ∃ final events indices, NativeFlow.Runs cfg ctx (program count left right output scratch) start events indices final ∧
      (∀ t, final.halted t=true) ∧ (final.core.lanes 0).pc=104 ∧ (∀ e∈events, TailEvent word e) := by
  let targets := fun t => Tail.target (NativeFlow.lane start t) output word t
  obtain ⟨events,indices,run,good⟩ := NativeFlow.Serial.run_lanes start targets (TailEvent word)
    (fun thread state same barrierEq siteEq => by
      have eq : state.core.lanes thread=start.core.lanes thread := congrArg Flow.State.core same
      have isLive : state.halted thread=false := (congrArg Flow.State.halted same).trans (ready.2.2.1 thread)
      have shared : Valid64 (state.core.lanes thread).sharedStart (state.core.lanes thread).sharedBytes
          ((state.core.lanes thread).regs 3).toNat := by
        rw [eq,(ready.1 thread).1]
        exact ⟨by rw [(ready.1 thread).2.2.1],aligned,
          by rw [(ready.1 thread).2.2.1]; have := (ready.1 thread).2.2.2.1; omega,
          by rw [(ready.1 thread).2.2.1]; exact (ready.1 thread).2.2.2.2⟩
      have localRun := Tail.lane_run (cfg:=cfg) (ctx:=ctx) (word:=word) (count:=count) (left:=left) (right:=right) (scratch:=scratch)
        state thread (eq ▸ ready.2.1 thread) (eq ▸ (ready.1 thread).2.1)
        (by rw [barrierEq,ready.2.2.2.1]; rfl) isLive shared (eq ▸ outputs thread)
      refine ⟨(Tail.records (NativeFlow.lane start thread) output word thread).map (Event.data thread),[],?_,?_⟩
      · simpa only [same,targets] using localRun
      · intro e member
        obtain ⟨a,ha,rfl⟩ := List.mem_map.mp member
        unfold Tail.records at ha
        split at ha
        · rename_i zero
          have owner : thread=0 := Fin.ext zero
          simp only [Tail.events,List.mem_cons,List.not_mem_nil,or_false] at ha
          rcases ha with rfl | rfl
          · exact ⟨owner,rfl,Or.inl ⟨rfl,rfl,by rw [Tail.guard_pc]; exact congrArg (·+2) (ready.2.1 thread)⟩⟩
          · exact ⟨owner,rfl,Or.inr ⟨rfl,rfl,by rw [Tail.guard_pc]; change (start.core.lanes thread).pc+2+4=102; rw [ready.2.1]⟩⟩
        · simp at ha)
  refine ⟨NativeFlow.Serial.allLanes start targets,events,indices,run,
    fun t => Tail.target_halted (ready.1 t).2.1 (ready.2.2.1 t),?_,good⟩
  simp [NativeFlow.Serial.allLanes,targets,Tail.target,Flow.halt,Flow.next,Tail.finish,
    Tail.prepared,put,assign,advance,Tail.guard_core,NativeFlow.lane,ready.2.1]

end PtxTorchLean.Poisson.PTX.Concurrent.Dot.Witness

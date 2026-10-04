import PoissonPTX.ObservedExists
import PoissonPTX.VectorFlowEntry

namespace PtxTorchLean.Poisson.PTX.Flow.Observed

/-- Instructions that produce no word or index memory observation. -/
def pure : Flow.Instr → Bool
  | .data (.load32 ..) | .data (.data (.load64 ..)) | .data (.data (.store64 ..)) => false
  | _ => true

theorem pure_eval (actual : Flow.Eval ctx i s t) (safe : pure i=true) : Eval ctx i s t none none := by
  cases actual with
  | simple ordinary => exact .simple ordinary
  | data actual =>
    cases actual with
    | mad32 => exact .data .mad32
    | wide4 => exact .data .wide4
    | load32 => simp [pure] at safe
    | data actual =>
      cases actual <;> try { exact .data (.data (.ordinary rfl (by constructor <;> assumption))) }
      all_goals simp [pure] at safe

theorem pure_observation (actual : Eval ctx i s t access index) (safe : pure i=true) : access=none ∧ index=none := by
  cases actual with
  | simple => exact ⟨rfl,rfl⟩
  | data actual =>
    cases actual with
    | mad32 => exact ⟨rfl,rfl⟩
    | wide4 => exact ⟨rfl,rfl⟩
    | load32 => simp [pure] at safe
    | data actual =>
      cases actual with
      | ordinary => exact ⟨rfl,rfl⟩
      | load => simp [pure] at safe
      | store => simp [pure] at safe

theorem pure_sequence (trace : Flow.Sequence ctx code s t)
    (safe : ∀ i∈code, pure i=true) (forward : ∀ i∈code, Flow.linear i=true)
    (pre post : List Flow.Instr) (pc : s.core.pc=pre.length) :
    Runs ctx (pre++code++post) s [] [] t := by
  induction trace generalizing pre with
  | nil => exact .nil
  | @cons i s middle code t running actual rest ih =>
    have nextPC : middle.core.pc=(pre++[i]).length := by
      rw [Flow.linear_pc actual (forward i (by simp)),pc]; simp
    have later := ih (fun i member => safe i (by simp [member]))
      (fun i member => forward i (by simp [member])) (pre++[i]) nextPC
    simpa only [List.append_assoc,List.singleton_append,Option.toList_none,List.nil_append] using Runs.cons
      (access:=none) (index:=none) ⟨running,i,by simp [pc],pure_eval actual (safe i (by simp))⟩ later

theorem vector_padding (pc : s.core.pc=0) (running : s.halted=false)
    (inactive : ¬Kernel.Residual.live ctx count) :
    Runs ctx (VectorFlowEntry.program count body) s [] [] (Assembly.setup ctx count s) ∧
      (Assembly.setup ctx count s).halted=true := by
  refine ⟨?_,Assembly.setup_inactive inactive⟩
  simpa only [VectorFlowEntry.program,List.nil_append,List.append_assoc] using
    pure_sequence (Flow.sequence_sound (Assembly.prologue_execution (ctx:=ctx) (count:=count) running))
      (by simp [Assembly.prologue,pure]) (by simp [Assembly.prologue,Flow.linear]) [] (body++[.ret]) pc

end PtxTorchLean.Poisson.PTX.Flow.Observed

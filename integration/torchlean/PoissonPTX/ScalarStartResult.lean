import PoissonPTX.ScalarStartValues
import PoissonPTX.ScalarArithmetic

namespace PtxTorchLean.Poisson.PTX.Scalar.Start
variable {a : Arena} {s : Flow.State} {norm product tolerance value : Word}

theorem scaled_ready (ready : a.Ready s) : a.Ready (scaled s value) := by
  simpa [Arena.Ready,scaled,assign,advance] using ready

theorem maximum_ready (ready : a.Ready s) : a.Ready (maximumStored s value) := by
  simpa [Arena.Ready,maximumStored,assign,advance] using ready

def Result (a : Arena) (s final : Flow.State) : Prop := ∃ norm product tolerance,
  decode norm=Float.sqrt (decode (read64 s.core.global (a.slot .rhsSquare))) ∧
  decode product=decode (read64 s.core.global (a.slot .rtol))*decode norm ∧
  decode tolerance=maximum product (read64 s.core.global (a.slot .atol)) ∧
  final=finished a (maximumStored (scaled (middle a (rooted a s norm)) product) tolerance)

theorem body_result (actual : Sequence ctx (body a.offset) s final) (running : s.halted=false) (ready : a.Ready s) :
    Result a s final := by
  have form : body a.offset=load64Code 4 (a.offset .rhsSquare)++([.sqrt 4 (.reg 4)]++
      (middleCode a.offset++([.base (.data (.data (.fp .mul 5 (.reg 5) (.reg 4))))]++
      ([.max 5 (.reg 5) (.reg 6)]++tailCode a.offset)))) := by simp [body,List.append_assoc]
  rw [form] at actual
  obtain ⟨loaded,loadRun,rest⟩ := sequence_split _ _ actual
  have same := load64_state loadRun
  subst loaded
  obtain ⟨root,rootRun,rest⟩ := sequence_split _ _ rest
  obtain ⟨norm,rootEq,normAllowed⟩ := sqrt_result rootRun
  have rootSame : root=rooted a s norm := rootEq
  rw [rootSame] at rest
  have rootReady : a.Ready (rooted a s norm) := rooted_ready ready
  obtain ⟨inputs,inputRun,rest⟩ := sequence_split _ _ rest
  have inputSame := sequence_unique inputRun (middle_trace (ctx:=ctx) running rootReady) middle_plain
  subst inputs
  obtain ⟨scaledState,scaleRun,rest⟩ := sequence_split _ _ rest
  obtain ⟨product,scaleEq,productAllowed⟩ := fp_result scaleRun
  have scaleSame : scaledState=scaled (middle a (rooted a s norm)) product := scaleEq
  rw [scaleSame] at rest
  obtain ⟨maxState,maxRun,tail⟩ := sequence_split _ _ rest
  obtain ⟨tolerance,maxEq,toleranceAllowed⟩ := max_result maxRun
  have maxSame : maxState=maximumStored (scaled (middle a (rooted a s norm)) product) tolerance := maxEq
  rw [maxSame] at tail
  have nextReady := maximum_ready (value:=tolerance) (scaled_ready (value:=product) (middle_ready rootReady))
  have tailSame := sequence_unique tail (tail_trace (ctx:=ctx) running nextReady) tail_plain
  refine ⟨norm,product,tolerance,?_,?_,?_,tailSame⟩
  · simpa only [Operand.eval,loaded64_reg,a.state_address ready] using normAllowed
  · simp only [FP.Result,FP.apply,Operand.eval] at productAllowed
    rw [(middle_values rootReady).2.1,(middle_values rootReady).1] at productAllowed
    simpa only [rooted,Norm.rooted_frame.1,Norm.rooted_frame.2.2.2.2.2] using productAllowed
  · simp only [Operand.eval,scaled,assign,advance,Function.update_self,
      Function.update_of_ne (by decide : (6:Nat)≠5)] at toleranceAllowed
    rw [(middle_values rootReady).2.2.1] at toleranceAllowed
    simpa only [rooted,Norm.rooted_frame.1] using toleranceAllowed

end PtxTorchLean.Poisson.PTX.Scalar.Start

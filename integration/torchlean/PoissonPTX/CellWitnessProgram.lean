import PoissonPTX.CellConsumerProgram

namespace PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.Witness
open CellMiddle

def stageBody (width : Nat) (stage : Fin 4) : List Op :=
  match stage.val with
  | 0 => first width 0 (Checks.derivativeOffset width)
  | 1 => second width 0 (Checks.derivativeOffset width) (Checks.weightOffset width)
  | 2 => third width 0 (Checks.derivativeOffset width)
  | _ => body width

def startPC (width : Nat) (stage : Fin 4) : Nat :=
  match stage.val with
  | 0 => 0
  | 1 => (stageBody width 0).length+2
  | 2 => (stageBody width 0).length+(stageBody width 1).length+4
  | _ => (Checks.program width).length

def segment (width : Nat) (stage : Fin 4) : List Instr :=
  [.skip (width*width) (startPC width stage+1+(stageBody width stage).length)] ++
    (stageBody width stage).map .data ++ if stage.val<3 then [.sync 0] else []

def beforeCode (width : Nat) (stage : Fin 4) : List Instr :=
  match stage.val with
  | 0 => []
  | 1 => segment width 0
  | 2 => segment width 0++segment width 1
  | _ => segment width 0++segment width 1++segment width 2

def afterCode (width : Nat) (stage : Fin 4) : List Instr :=
  match stage.val with
  | 0 => segment width 1++segment width 2++segment width 3
  | 1 => segment width 2++segment width 3
  | 2 => segment width 3
  | _ => []

theorem before_length (stage : Fin 4) : (beforeCode width stage).length=startPC width stage := by
  fin_cases stage <;> simp [beforeCode,segment,startPC,stageBody,Checks.program,code,phase,List.length_append,Nat.add_assoc]

theorem segments (stage : Fin 4) :
    program width=beforeCode width stage++segment width stage++afterCode width stage := by
  fin_cases stage <;>
    simp [beforeCode,afterCode,segment,startPC,stageBody,program,suffix,Checks.program,code,phase,
      List.append_assoc,Nat.add_assoc]

theorem stage_guard (stage : Fin 4) :
    (program width)[startPC width stage]?=some (.skip (width*width) (startPC width stage+1+(stageBody width stage).length)) := by
  rw [segments stage,← before_length stage]
  simp [List.append_assoc,segment,before_length]

theorem stage_fetch (stage : Fin 4) (found : (stageBody width stage)[j]?=some op) :
    (program width)[startPC width stage+1+j]?=some (.data op) := by
  have bound := (List.getElem?_eq_some_iff.mp found).1
  rw [segments stage,List.append_assoc,List.getElem?_append_right
    (show (beforeCode width stage).length≤startPC width stage+1+j by rw [before_length]; omega)]
  rw [before_length,show startPC width stage+1+j-startPC width stage=j+1 by omega]
  simp only [segment,List.cons_append,List.nil_append,List.getElem?_cons_succ,List.append_assoc]
  rw [List.getElem?_append_left (by simpa using bound),List.getElem?_map,found]
  rfl

theorem stage_sync (stage : Fin 4) (earlier : stage.val<3) :
    (program width)[startPC width stage+1+(stageBody width stage).length]?=some (.sync 0) := by
  rw [segments stage,List.append_assoc,List.getElem?_append_right
    (show (beforeCode width stage).length≤startPC width stage+1+(stageBody width stage).length by rw [before_length]; omega)]
  rw [before_length,show startPC width stage+1+(stageBody width stage).length-startPC width stage=(stageBody width stage).length+1 by omega]
  simp [segment,earlier,List.append_assoc]

theorem next_stage (stage : Fin 3) :
    startPC width ⟨stage.val+1,by omega⟩=startPC width ⟨stage.val,by omega⟩+1+
      (stageBody width ⟨stage.val,by omega⟩).length+1 := by
  fin_cases stage <;> simp [startPC,stageBody,Checks.program,code,phase,Nat.add_assoc] <;> omega

theorem last_end : startPC width 3+1+(stageBody width 3).length=(program width).length := by
  simp [startPC,stageBody,program,suffix,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]

end PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.Witness

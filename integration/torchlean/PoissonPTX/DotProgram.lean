import PoissonPTX.NativeFlow
import PoissonPTX.DotInputText
import PoissonPTX.ReductionNativeText

/-! The complete emitted dot entry. The setup and input loop occupy positions
0..19, the shared tree 20..95, and the final conditional return/read/store 96..103.
All branches use absolute positions in this one program. -/
namespace PtxTorchLean.Poisson.PTX.Concurrent.Dot

def treeInstruction : Reduction.Native.Instr → NativeFlow.Instr
  | .data op => .flow (.data (.data op))
  | .compare count => .flow (.compare 0 .ge (.reg 14) (.imm (BitVec.ofNat 64 count)))
  | .branch target => .flow (.branch 0 true (20+target))
  | .sync resource => .sync resource

def tail (output : Word) : List Flow.Instr :=
  [.compare 0 .ne (.reg 14) (.imm 0),.predRet 0 true,
    .data (.data (.load64 .shared 8 (.reg 3))),
    .data (.data (.wide8 1 (.imm 0))),.data (.data (.add64 2 (.reg 0) (.reg 1))),
    .data (.data (.add64 2 (.reg 2) (.imm output))),
    .data (.data (.store64 .global (.reg 2) (.reg 8))),.ret]

def program (count : Nat) (left right output scratch : Word) : List NativeFlow.Instr :=
  (DotInput.inputProgram count left right scratch).map .flow ++
    Reduction.Native.code.map treeInstruction ++ (tail output).map .flow

theorem length : (program count left right output scratch).length=104 := by
  simp [program,DotInput.input_length,Reduction.Native.length,tail]

theorem input_fetch (before : pc<20) :
    (program count left right output scratch)[pc]?=
      (DotInput.inputProgram count left right scratch)[pc]?.map NativeFlow.Instr.flow := by
  simp [program,List.append_assoc,List.getElem?_append,DotInput.input_length,before]

theorem tree_fetch (inside : pc<76) :
    (program count left right output scratch)[20+pc]?=
      Reduction.Native.code[pc]?.map treeInstruction := by
  simp [program,List.getElem?_append,DotInput.input_length,Reduction.Native.length,
    inside,show ¬20+pc<20 by omega]

theorem tail_fetch :
    (program count left right output scratch)[96+pc]?=(tail output)[pc]?.map NativeFlow.Instr.flow := by
  simp [program,List.getElem?_append,DotInput.input_length,Reduction.Native.length,
    show ¬96+pc<20 by omega,show 96+pc-20=76+pc by omega,show ¬76+pc<76 by omega]

/-- The exact complete list contains no four-byte input-index instructions;
the generic machine still supports those for other entries. -/
def noIndex : NativeFlow.Instr → Bool
  | .flow (.data (.load32 ..)) => false
  | _ => true

theorem no_index_loads (member : i∈program count left right output scratch) : noIndex i=true := by
  simp only [program,List.mem_append,List.mem_map] at member
  rcases member with (⟨op,inside,rfl⟩ | ⟨op,inside,rfl⟩) | ⟨op,inside,rfl⟩
  · simp only [DotInput.inputProgram,Flow.OperandWindow.program,Flow.OperandWindow.header,
      DotInput.setupCode,DotInput.body,loadCode,addressCode,List.map_cons,List.map_nil,
      List.map_append,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at inside
    simp only [or_assoc] at inside
    rcases inside with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals rfl
  · cases op <;> rfl
  · simp only [tail,List.mem_cons,List.not_mem_nil,or_false] at inside
    rcases inside with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl

end PtxTorchLean.Poisson.PTX.Concurrent.Dot

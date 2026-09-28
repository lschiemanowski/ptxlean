import PtxBinary32.GridDenseProgram
import Lean

/-! Restricted, executable export of the existing compact dense instruction list.
This serializer is not a verified compiler. Address relocation and entry setup
are explicit additions, retained separately in the export manifest. -/
namespace Ptx.Hardware.Dense
open Ptx.Scalar Ptx.Scalar.Parallel
open Lean

def guard : Scalar.Guard → String
  | .always => ""
  | .pred i true => s!"@%p{i} "
  | .pred i false => s!"@!%p{i} "

def word : Operand32 → String
  | .reg i => s!"%r{i}"
  | .imm v => toString v.toNat

def address : Operand64 → String
  | .reg i => s!"%a{i}"
  | .imm v => toString v.toNat

def floatWord : Operand32 → String
  | .reg i => s!"%r{i}"
  | .imm v => "0f" ++ String.ofList ((List.range 8).reverse.map fun k =>
      ("0123456789abcdef".toList[v.toNat / 16^k % 16]!))

def scalar (i : Scalar.Instr) : Except String (List String) := do
  let body ← match i.op with
    | .mov32 d a => pure s!"mov.b32 %r{d}, {word a};"
    | .bin32 op d a b =>
      let mnemonic ← match op with
        | .and => pure "and.b32"
        | .shr => pure "shr.u32"
        | .mulLo => pure "mul.lo.u32"
        | .add => pure "add.u32"
        | _ => throw "unsupported integer binary operation"
      pure s!"{mnemonic} %r{d}, {word a}, {word b};"
    | .cvt64 d a => pure s!"cvt.u64.u32 %a{d}, {word a};"
    | .add64 d a b => pure s!"add.u64 %a{d}, {address a}, {address b};"
    | .setp cmp d a b =>
      let cmp ← match cmp with
        | .lt => pure "lt" | .eq => pure "eq" | .ge => pure "ge"
        | _ => throw "unsupported comparison"
      pure s!"setp.{cmp}.u32 %p{d}, {word a}, {word b};"
    | _ => throw "unsupported local instruction"
  pure [guard i.guard ++ body]

/-- Address registers retain the model's byte offsets. A fresh temporary adds
only the selected allocation base at the actual memory instruction. -/
def instruction : Parallel.Instr → Except String (List String)
  | .localStep i => scalar i
  | .memory space i => do
      let (suffix,base) := match space with
        | .global => ("relaxed.gpu.global","%globalBase") | .shared => ("relaxed.cta.shared","%sharedBase")
      let (a,body) ← match i.op with
        | .load d a => pure (a,s!"ld.{suffix}.b32 %r{d}, [%effective];")
        | .store a v => pure (a,s!"st.{suffix}.b32 [%effective], {word v};")
        | _ => throw "unsupported memory instruction"
      pure [s!"{guard i.guard}add.u64 %effective, {base}, {address a};",guard i.guard ++ body]
  | .binary32 i =>
      let mnemonic := match i.operation with | .add => "add" | .mul => "mul"
      pure [s!"{guard i.guard}{mnemonic}.rn.f32 %r{i.destination}, {floatWord i.left}, {floatWord i.right};"]
  | .sync resource => if resource.val=0 then pure ["bar.sync 0;"] else throw "unsupported barrier"
  | .exit => pure ["exit;"]

/-- Export one fixed shape. The same `Compact.program` is used by the existing
universal grid-forward theorem. No Python implementation reconstructs its body. -/
def exportCase (request : Json) : Except String Json := do
  let rows ← request.getObjValAs? Nat "rows"
  let columns ← request.getObjValAs? Nat "columns"
  let depth ← request.getObjValAs? Nat "depth"
  if depth > 10 then throw "depth exceeds 10"
  if h : columns ≤ 2^depth then
    let s : Scalar.Parallel.Dense.Shape := ⟨rows,columns,depth,h,true⟩
    if s.globalWords+s.sharedWords+2*s.width ≥ 2^30 then
      throw "shape exceeds conservative represented-address limits"
    let input ← request.getObjValAs? (Array Nat) "words"
    if input.size != s.outputBase then throw "incorrect input word count"
    if input.any (fun w => w ≥ 2^32) then throw "not a binary32 word"
    let global := input.toList.map (BitVec.ofNat 32) ++ List.replicate rows 0xdeadbeef
    let body ← (Scalar.Parallel.Dense.Compact.program s).mapM instruction
    let sites := (Scalar.Parallel.Dense.Compact.program s).zipIdx |>.map fun (i,pc) =>
      Json.mkObj [("pc",toJson pc),("formal",toJson (reprStr i)),("ptx",toJson body[pc]!)]
    let expected := (List.range rows).map fun row =>
      (Scalar.Parallel.Dense.forwardWord s global row).toNat
    pure <| Json.mkObj [("rows",toJson rows),("columns",toJson columns),("depth",toJson depth),
      ("width",toJson s.width),("shared_words",toJson (Scalar.Parallel.Dense.Compact.sharedWords s)),
      ("output_base",toJson s.outputBase),("global_words",toJson s.globalWords),
      ("program",toJson sites),("expected",toJson expected)]
  else throw "columns exceed padded width"

end Ptx.Hardware.Dense

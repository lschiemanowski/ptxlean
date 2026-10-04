import PoissonPTX.ScalarNorm
import PoissonPTX.ScalarRestartFlag
import PoissonPTX.AssemblyText

namespace PtxTorchLean.Poisson.PTX.Scalar.Text

def register (r : Nat) : String := if r=22 then "%flag2" else Assembly.Text.register r

def operand : Operand → String
  | .reg r => register r
  | .imm w => toString w.toNat
  | .offset r w => s!"{register r}+{w.toNat}"

/-- The emitted scalar programs use only these exact floating literals. Other
words receive an explicit unmatched marker, rather than a guessed rendering. -/
def floating : Operand → String
  | .imm 0 => "0d0000000000000000"
  | .imm 0x7fefffffffffffff => "0d7fefffffffffffff"
  | .imm w => s!"unreviewed-f64-{w.toNat}"
  | op => operand op

def data : Op → String
  | .mov dst src => s!"mov.f64 {register dst}, {floating src};"
  | .mul32 dst a b => s!"mul.lo.u32 {register dst}, {operand a}, {operand b};"
  | .add32 dst a b => s!"add.u32 {register dst}, {operand a}, {operand b};"
  | .add64 dst a b => s!"add.u64 {register dst}, {operand a}, {operand b};"
  | .wide8 dst i => s!"mul.wide.u32 {register dst}, {operand i}, 8;"
  | .load64 sp dst addr => s!"ld.{PTX.Text.space sp}.f64 {register dst}, [{operand addr}];"
  | .store64 sp addr src => s!"st.{PTX.Text.space sp}.f64 [{operand addr}], {floating src};"
  | .fp op dst a b => s!"{PTX.Text.operation op} {register dst}, {floating a}, {floating b};"

def indexed : Indexed.Instr → String
  | .data op => data op
  | .mad32 dst a scale b => s!"mad.lo.u32 {register dst}, {register a}, {scale.toNat}, {register b};"
  | .wide4 dst src => s!"mul.wide.u32 {register dst}, {register src}, 4;"
  | .load32 dst addr => s!"ld.global.u32 {register dst}, [{register addr}];"

def base : Flow.Instr → String
  | .data op => indexed op
  | .context dst .arena => s!"ld.param.u64 {register dst}, [arena];"
  | .context dst src => s!"mov.u32 {register dst}, {Assembly.Text.source src};"
  | .compare p cmp a b => s!"setp.{Assembly.Text.comparison cmp}.u32 %p{p}, {operand a}, {operand b};"
  | .ret => "ret;"
  | _ => "unreviewed-scalar-control"

def instruction : Instr → String
  | .base i => base i
  | .sqrt dst a => s!"sqrt.rn.f64 {register dst}, {floating a};"
  | .abs dst a => s!"abs.f64 {register dst}, {floating a};"
  | .max dst a b => s!"max.f64 {register dst}, {floating a}, {floating b};"
  | .compare dst cmp a b => s!"setp.{match cmp with | .gt => "gt" | .le => "le"}.f64 %p{dst}, {floating a}, {floating b};"
  | .equal32 dst a b => s!"setp.eq.u32 %p{dst}, {operand a}, {operand b};"
  | .andPred dst a b => s!"and.pred %p{dst}, %p{a}, %p{b};"
  | .notPred dst a => s!"not.pred %p{dst}, %p{a};"
  | .select32 dst a b p => s!"selp.u32 {register dst}, {operand a}, {operand b}, %p{p};"
  | .move32 p yes dst a => s!"@{if yes then "" else "!"}%p{p} mov.u32 {register dst}, {operand a};"
  | .wide4 dst a => s!"mul.wide.u32 {register dst}, {operand a}, 4;"
  | .store32 addr a => s!"st.global.u32 [{operand addr}], {operand a};"
  | .predFP p yes op dst a b => s!"@{if yes then "" else "!"}%p{p} {PTX.Text.operation op} {register dst}, {floating a}, {floating b};"

def norm (source output : Word) : List String := (Norm.entry source output).map instruction
def restartFlag (active : Word) : List String := (RestartFlag.entry active).map instruction

end PtxTorchLean.Poisson.PTX.Scalar.Text

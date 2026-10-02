import PoissonPTX.ResidualKernel
import Lean

/-! Rendering for the reviewed true_residual instruction list. Matching emitted
text is a frontend check, separate from the Lean instruction-execution proof. -/
namespace PtxTorchLean.Poisson.PTX.Text

def register : Nat → String
  | 0 => "%base" | 1 => "%off" | 2 => "%addr" | 3 => "%shared"
  | 4 => "%a" | 5 => "%b" | 6 => "%c" | 7 => "%d"
  | 8 => "%acc" | 9 => "%acc2" | 10 => "%prod" | 11 => "%value"
  | 12 => "%global" | 13 => "%idx" | 14 => "%lane" | 15 => "%cell"
  | 16 => "%i" | 17 => "%j" | 18 => "%node"
  | n => s!"%unmapped{n}"

def operand : Operand → String
  | .reg r => register r
  | .imm w => toString w.toNat
  | .offset r w => s!"{register r}+{w.toNat}"

def operation : FP → String
  | .add => "add.rn.f64" | .sub => "sub.rn.f64"
  | .mul => "mul.rn.f64" | .div => "div.rn.f64"

def space : Space → String | .global => "global" | .shared => "shared"

def data : Op → String
  | .mov d s => s!"mov.b64 {register d}, {operand s};"
  | .mul32 d a b => s!"mul.lo.u32 {register d}, {operand a}, {operand b};"
  | .add32 d a b => s!"add.u32 {register d}, {operand a}, {operand b};"
  | .add64 d a b => s!"add.u64 {register d}, {operand a}, {operand b};"
  | .wide8 d i => s!"mul.wide.u32 {register d}, {operand i}, 8;"
  | .load64 sp d a => s!"ld.{space sp}.f64 {register d}, [{operand a}];"
  | .store64 sp a s => s!"st.{space sp}.f64 [{operand a}], {operand s};"
  | .fp op d a b => s!"{operation op} {register d}, {operand a}, {operand b};"

def instruction : Kernel.Instr → String
  | .parameter d => s!"ld.param.u64 {register d}, [arena];"
  | .lane d => s!"mov.u32 {register d}, %tid.x;"
  | .group d => s!"mov.u32 {register d}, %ctaid.x;"
  | .mad32 d a scale b => s!"mad.lo.u32 {register d}, {register a}, {scale.toNat}, {register b};"
  | .ge32 a limit => s!"setp.ge.u32 %p0, {register a}, {limit.toNat};"
  | .predRet => "@%p0 ret;"
  | .data op => data op
  | .ret => "ret;"

/-- Uses the very same parameterized program as fetched_correct. -/
def residual (count : BitVec 32) (rhs ap output : Word) : List String :=
  (Kernel.Residual.program count rhs ap output).map instruction

end PtxTorchLean.Poisson.PTX.Text

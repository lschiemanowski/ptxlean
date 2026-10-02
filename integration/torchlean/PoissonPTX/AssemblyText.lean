import PoissonPTX.AssemblyLoop
import PoissonPTX.Text

namespace PtxTorchLean.Poisson.PTX.Assembly.Text

def register : Nat → String
  | 19 => "%cursor"
  | 20 => "%end"
  | 21 => "%flag"
  | r => PTX.Text.register r

def operand : Operand → String
  | .reg r => register r
  | .imm w => toString w.toNat
  | .offset r w => s!"{register r}+{w.toNat}"

def data : Op → String
  | .mov dst src => s!"mov.b64 {register dst}, {operand src};"
  | .mul32 dst a b => s!"mul.lo.u32 {register dst}, {operand a}, {operand b};"
  | .add32 dst a b => s!"add.u32 {register dst}, {operand a}, {operand b};"
  | .add64 dst a b => s!"add.u64 {register dst}, {operand a}, {operand b};"
  | .wide8 dst i => s!"mul.wide.u32 {register dst}, {operand i}, 8;"
  | .load64 space dst addr => s!"ld.{PTX.Text.space space}.f64 {register dst}, [{operand addr}];"
  | .store64 space addr src => s!"st.{PTX.Text.space space}.f64 [{operand addr}], {operand src};"
  | .fp op dst a b => s!"{PTX.Text.operation op} {register dst}, {operand a}, {operand b};"

def indexed : Indexed.Instr → String
  | .data op => data op
  | .mad32 dst a scale b => s!"mad.lo.u32 {register dst}, {register a}, {scale.toNat}, {register b};"
  | .wide4 dst src => s!"mul.wide.u32 {register dst}, {register src}, 4;"
  | .load32 dst addr => s!"ld.global.u32 {register dst}, [{register addr}];"

def label (finish target : Nat) : String := if target=0 then "loop" else if target=finish then "done" else s!"pc_{target}"
def comparison : Flow.Compare → String | .ge => "ge" | .ne => "ne" | .lt => "lt"
def source : Flow.Source → String | .arena => "arena" | .lane => "%tid.x" | .group => "%ctaid.x"

def instruction (finish : Nat) : Flow.Instr → String
  | .data op => indexed op
  | .context dst .arena => s!"ld.param.u64 {register dst}, [arena];"
  | .context dst src => s!"mov.u32 {register dst}, {source src};"
  | .compare p cmp a b => s!"setp.{comparison cmp}.u32 %p{p}, {operand a}, {operand b};"
  | .branch p yes target => s!"@{if yes then "" else "!"}%p{p} bra {label finish target};"
  | .jump target => s!"bra {label finish target};"
  | .select p yes dst value => s!"@{if yes then "" else "!"}%p{p} mov.b64 {register dst}, {operand value};"
  | .predRet p yes => s!"@{if yes then "" else "!"}%p{p} ret;"
  | .ret => "ret;"

/-- Bind the loop slice up to its exit label. The isolated theorem's terminal
ret is replaced by the masking/store continuation in the emitted entry. The
separate full-entry renderer binds that continuation and the absolute counters. -/
def rendered (entries element : Word) : List String :=
  ["loop:"]++((Flow.Loop.program 19 20 (body entries element)).dropLast.map
    (instruction ((body entries element).length+3)))++["done:"]

end PtxTorchLean.Poisson.PTX.Assembly.Text

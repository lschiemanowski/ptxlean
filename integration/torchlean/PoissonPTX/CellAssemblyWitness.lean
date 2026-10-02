import PoissonPTX.CellAssembly
import PoissonPTX.CellWholeZero
import PoissonPTX.SourceCheckWords
import PoissonPTX.AssemblyTableCheck

namespace PtxTorchLean.Poisson.PTX.CellAssemblyWitness
set_option maxRecDepth 100000
set_option maxHeartbeats 80000000

def one : Word := 0x3ff0000000000000

/-- Synthetic nonzero two-by-two cell: identity coefficient matrices, unit
weights and unit gathered values. The cell produces four twos, whose single
node assembles to eight. Metadata and data use distinct physical byte fields. -/
def memory : Memory :=
  write32 (write32 (write32 (write32
    ([0,24,64,88,128,136,144,152,224].foldl (fun m p => write64 m p one) (fun _ => 0))
    212 4) 244 1) 248 2) 252 3

def operator : Operator where
  mesh := ⟨1,1,#[(0,0)],#[#[0,0,0,0]],#[false],#[0]⟩
  nodes := #[0,1]
  q := #[0,1]
  weights := #[1,1]
  b := matrix fun i j => if i=j then 1 else 0
  d := matrix fun i j => if i=j then 1 else 0
  w := matrix fun _ _ => 1
  diagonal := #[0]

def values : Array Float := #[1]
def seed : PTX.State := {CellWhole.Zero.seed with global:=memory}
def start : CellEntry.State 32 := ⟨⟨fun _ => seed,Ptx.Barrier.reset 0,none⟩,fun _ => false⟩
def cfg := CellWhole.Zero.cfg
def bases := CellWhole.Zero.bases
def context := CellWhole.Zero.ctx

def prefixChoice (_ : Fin 32) (s : PTX.State) : Word :=
  if s.pc=12 then (read32 s.global (s.regs 2).toNat).setWidth 64 else read64 s.global (s.regs 2).toNat

def prefixCandidate := CellEntry.execute cfg (CellPrologue.threadContext bases 0)
  (CellEntry.program 2 192 224) prefixChoice CellEntry.Checks.schedule start

def prefixResult : CellEntry.Outcome 32 := prefixCandidate.getD ⟨start,[],[]⟩

theorem prefix_executed : prefixCandidate=some prefixResult := by
  have yes : prefixCandidate.isSome=true := by decide +kernel
  cases h : prefixCandidate with
  | none => simp [h] at yes
  | some out => simp [prefixResult,h]

/-- Address-only witness generator. The actual execution and source checks
below independently check its proposed load words. -/
def addressSeed (thread : Fin 32) : PTX.State :=
  {seed with regs := fun r =>
    if r=14 then BitVec.ofNat 64 thread.val else
    if r=16 then BitVec.ofNat 64 (thread.val/2) else
    if r=17 then BitVec.ofNat 64 (thread.val%2) else 0}

def addressStep (s : PTX.State) : Concurrent.Instr → PTX.State
  | .data (.mov dst src) => assign s dst (src.eval s)
  | .data (.mul32 dst a b) => assign s dst (mul32 (a.eval s) (b.eval s))
  | .data (.add32 dst a b) => assign s dst (add32 (a.eval s) (b.eval s))
  | .data (.add64 dst a b) => assign s dst (a.eval s+b.eval s)
  | .data (.wide8 dst index) => assign s dst (BitVec.ofNat 64 ((index.eval s).toNat%2^32*8))
  | _ => advance s

def addressState (thread : Fin 32) (pc : Nat) : PTX.State :=
  ((Concurrent.CellConsumer.WithOutput.front 2).take pc).foldl addressStep (addressSeed thread)

/-- Shared loads propose one; source compatibility checks the bytes against
actual stores in the full history. Global loads use the address-only generator. -/
def bodyChoice (thread : Fin 32) (pc : Nat) : Word :=
  match (Concurrent.CellConsumer.WithOutput.front 2)[pc]? with
  | some (.data (.load64 .global _ addr)) => read64 memory (addr.eval (addressState thread pc)).toNat
  | some (.data (.load64 .shared _ _)) => one
  | _ => 0

def bodyStart := CellEntry.continuation prefixResult.state
def bodyCandidate := Concurrent.WithTail.execute cfg context (Concurrent.CellConsumer.WithOutput.front 2)
  (CellFinal.tail 2 256) bodyChoice Concurrent.CellConsumer.WithOutput.Checks.schedule bodyStart

def bodyResult : Concurrent.WithTail.Outcome 32 := bodyCandidate.getD ⟨bodyStart,[]⟩

theorem body_executed : bodyCandidate=some bodyResult := by
  have yes : bodyCandidate.isSome=true := by decide +kernel
  cases h : bodyCandidate with
  | none => simp [h] at yes
  | some out => simp [bodyResult,h]

def events := prefixResult.events++bodyResult.events.map (Relocate.event 21)
def final := Relocate.tailState 21 bodyResult.state

attribute [local irreducible] prefixResult bodyResult events final

theorem actual : CellWhole.Runs cfg bases 0 2 192 224 256 context (CellWhole.begin start)
    events prefixResult.indices final := by
  unfold events final
  exact CellWhole.compose (CellEntry.execute_sound prefix_executed) (by decide +kernel) (by decide +kernel)
    (Concurrent.WithTail.execute_sound body_executed)

theorem returned : ∀ t : Fin 32, final.halted t=true ∧
    (final.core.lanes t).pc=21+(Concurrent.CellConsumer.WithOutput.front 2).length+6 := by decide +kernel

def initial : Space → Memory | .global => memory | .shared => fun _ => 0

theorem admitted : Concurrent.Visibility.Compatible initial events (Concurrent.ZeroSources.source events) :=
  Concurrent.WordSourceCheck.sound (by decide +kernel)

theorem aligned : ∀ owner a, Concurrent.Event.data owner a∈events → a.data.address%8=0 := by
  have checked : events.all (fun e => match e with | .data _ a => a.data.address%8==0 | _ => true)=true := by decide +kernel
  intro owner a member
  simpa using List.all_eq_true.mp checked (.data owner a) member

theorem performed : Concurrent.Visibility.Performed events (Concurrent.ZeroSources.source events) := by
  intro w r writer reader wa ra hw hr write read sw sr ordered j k same
  have aw := aligned writer wa (List.mem_of_getElem? hw)
  have ar := aligned reader ra (List.mem_of_getElem? hr)
  have hj := j.isLt; have hk := k.isLt
  have addr : wa.data.address=ra.data.address := by omega
  have found : events.findIdx (Concurrent.ZeroSources.writes ra.space ra.data.address)<events.length := by
    apply List.findIdx_lt_length.mpr
    exact ⟨.data writer wa,List.mem_of_getElem? hw,by simp [Concurrent.ZeroSources.writes,write,sw,sr,addr]⟩
  simp [Concurrent.ZeroSources.source,hr,found]

theorem indices_admitted : IndexSources.Compatible memory events prefixResult.indices (fun _ _ => .initial) := by
  have checked : prefixResult.indices.all (fun (_,a) => decide (∀ k : Fin 4,
      IndexSources.byte32 a.value k.val=memory (a.address+k.val)))=true := by decide +kernel
  intro r owner a observed k
  have h := List.all_eq_true.mp checked (owner,a) (List.mem_of_getElem? observed)
  exact (of_decide_eq_true h) k

end PtxTorchLean.Poisson.PTX.CellAssemblyWitness

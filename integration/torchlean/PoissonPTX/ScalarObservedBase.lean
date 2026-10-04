import PoissonPTX.ScalarObservedSegments
import PoissonPTX.ScalarArena

namespace PtxTorchLean.Poisson.PTX.Scalar.Observed

def dataKeepsBase : Op → Bool
  | .store64 .. => true
  | .mov dst .. | .mul32 dst .. | .add32 dst .. | .add64 dst .. | .wide8 dst .. | .load64 _ dst .. | .fp _ dst .. => dst != 0

def indexedKeepsBase : Indexed.Instr → Bool
  | .data op => dataKeepsBase op
  | .mad32 dst .. | .wide4 dst .. | .load32 dst .. => dst != 0

def keepsBase : Instr → Bool
  | .base (.data op) => indexedKeepsBase op
  | .base (.context dst _) | .base (.select _ _ dst _) => dst != 0
  | .sqrt dst .. | .abs dst .. | .max dst .. | .select32 dst .. | .move32 _ _ dst .. | .wide4 dst .. | .predFP _ _ _ dst .. => dst != 0
  | _ => true

theorem data_base_frame (actual : Indexed.Candidate.Data op s t word index) (safe : indexedKeepsBase op=true) :
    t.regs 0=s.regs 0 ∧ t.globalStart=s.globalStart ∧ t.globalBytes=s.globalBytes := by
  cases actual with
  | data actual =>
    cases actual with
    | ordinary ordinary actual =>
      cases actual <;> simp_all [Concurrent.ordinary,indexedKeepsBase,dataKeepsBase,assign,advance,ne_comm]
    | load => simp_all [indexedKeepsBase,dataKeepsBase,assign,advance,ne_comm]
    | @store sp => cases sp <;> exact ⟨rfl,rfl,rfl⟩
  | _ => simp_all [indexedKeepsBase,assign,advance,ne_comm]

theorem extra_base_frame (actual : Scalar.Eval ctx i s t) (plain : extra i=true) (safe : keepsBase i=true) :
    t.core.regs 0=s.core.regs 0 ∧ t.core.globalStart=s.core.globalStart ∧ t.core.globalBytes=s.core.globalBytes := by
  cases actual with
  | base => simp [extra] at plain
  | store32 => simp [extra] at plain
  | simple ordinary =>
    cases i <;> simp_all [Scalar.ordinary,extra,keepsBase,Scalar.simple,assign,advance,Flow.next,ne_comm]
    split <;> simp_all [ne_comm]
  | _ => simp_all [keepsBase,assign,advance,Flow.next,ne_comm]

theorem eval_base_frame (actual : Eval ctx i s t events) (safe : keepsBase i=true) :
    t.core.regs 0=s.core.regs 0 ∧ t.core.globalStart=s.core.globalStart ∧ t.core.globalBytes=s.core.globalBytes := by
  cases actual with
  | extra plain actual => exact extra_base_frame actual plain safe
  | store32 => exact ⟨rfl,rfl,rfl⟩
  | base actual =>
    cases actual with
    | data actual => exact data_base_frame actual safe
    | simple ordinary =>
      rename_i op
      cases op <;> simp_all [keepsBase,Flow.simple,Flow.next,Flow.halt,Flow.goto,assign,advance,ne_comm]
      all_goals split <;> simp_all [ne_comm]

theorem sequence_base_frame (actual : Sequence ctx code s events t) (safe : ∀ i∈code, keepsBase i=true) :
    t.core.regs 0=s.core.regs 0 ∧ t.core.globalStart=s.core.globalStart ∧ t.core.globalBytes=s.core.globalBytes := by
  induction actual with
  | nil => exact ⟨rfl,rfl,rfl⟩
  | cons alive step rest ih =>
    have one := eval_base_frame step (safe _ (by simp))
    have two := ih (fun i mem => safe i (by simp [mem]))
    exact ⟨two.1.trans one.1,two.2.1.trans one.2.1,two.2.2.trans one.2.2⟩

theorem sequence_ready {a : Arena} (actual : Sequence ctx code s events t) (safe : ∀ i∈code, keepsBase i=true)
    (ready : a.Ready s) : a.Ready t := by
  have frame := sequence_base_frame actual safe
  exact ⟨frame.1.trans ready.1,frame.2.1.trans ready.2.1,frame.2.2.trans ready.2.2⟩

end PtxTorchLean.Poisson.PTX.Scalar.Observed

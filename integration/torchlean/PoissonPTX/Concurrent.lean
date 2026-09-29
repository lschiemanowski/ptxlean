import PoissonPTX.Sources
import PoissonPTX.Machine
import Ptx.Barrier

/-! Fetched binary64 candidate execution. Loads can choose arbitrary words;
source admission is deliberately separate from instruction execution. Only
resource zero, full-block synchronization, and explicit no-exit fragments are
supported for barrier theorems. Global and shared byte spaces remain distinct. -/
namespace PtxTorchLean.Poisson.PTX.Concurrent

structure Access where
  space : Space
  data : Sources.Access
  deriving DecidableEq, Repr

def ordinary : Op → Bool
  | .load64 .. | .store64 .. => false
  | _ => true

inductive Data : Op → PTX.State → PTX.State → Option Access → Prop where
  | ordinary (plain : ordinary op=true) (h : Eval op s t) : Data op s t none
  | load (valid : Valid64 (s.start sp) (s.bytes sp) (addr.eval s).toNat) :
      Data (.load64 sp dst addr) s (assign s dst word)
        (some ⟨sp,⟨s.pc,false,(addr.eval s).toNat,word⟩⟩)
  | store (valid : Valid64 (s.start sp) (s.bytes sp) (addr.eval s).toNat) :
      Data (.store64 sp addr src) s (put s sp (addr.eval s).toNat (src.eval s))
        (some ⟨sp,⟨s.pc,true,(addr.eval s).toNat,src.eval s⟩⟩)

theorem data_pc (h : Data op s t access) : t.pc=s.pc+1 := by
  cases h with
  | ordinary _ he => exact eval_pc he
  | load => rfl
  | store => cases ‹Space› <;> rfl

inductive Instr where
  | data (op : Op)
  | skip (active : Nat) (target : Nat)
  | sync (resource : Fin 16)
  deriving DecidableEq, Repr

structure Config (n : Nat) where
  cta : Nat
  nonempty : 0<n

structure State (n : Nat) where
  lanes : Fin n → PTX.State
  barrier : Ptx.Barrier.State n
  site : Option Nat

inductive Event (n : Nat) where
  | data (thread : Fin n) (access : Access)
  | barrier (event : Ptx.Barrier.Event n)
  deriving DecidableEq, Repr

structure Outcome (n : Nat) where
  state : State n
  events : List (Event n)

def setLane (s : State n) (thread : Fin n) (lane : PTX.State) : State n :=
  {s with lanes := Function.update s.lanes thread lane}

def barrierConfig (cfg : Config n) (s : State n) (thread : Fin n) : Ptx.Barrier.Config n :=
  ⟨cfg.cta,0,s.site.getD (s.lanes thread).pc,cfg.nonempty⟩

def barrierRequest (cfg : Config n) (s : State n) (thread : Fin n) (resource : Fin 16) : Ptx.Barrier.Request n :=
  ⟨⟨cfg.cta,resource,s.barrier.generation,(s.lanes thread).pc⟩,thread⟩

def synchronize (cfg : Config n) (s : State n) (thread : Fin n) (resource : Fin 16) : Outcome n :=
  let config := barrierConfig cfg s thread
  let request := barrierRequest cfg s thread resource
  let result := Ptx.Barrier.step config s.barrier request
  match result.disposition with
  | .rejectedWrongKey => ⟨s,[]⟩
  | .waiting => ⟨{s with barrier := result.state,site := some config.site},result.events.map .barrier⟩
  | .released =>
    ⟨{s with barrier := result.state,site := none,lanes := fun t => advance (s.lanes t)},
      result.events.map .barrier⟩

inductive Dispatch (cfg : Config n) (thread : Fin n) : Instr → State n → Outcome n → Prop
  | data (h : Data op (s.lanes thread) next access) :
      Dispatch cfg thread (.data op) s
        ⟨setLane s thread next,(access.toList.map (Event.data thread))⟩
  | skip : Dispatch cfg thread (.skip active target) s
      ⟨setLane s thread {s.lanes thread with pc := if thread.val<active then (s.lanes thread).pc+1 else target},[]⟩
  | sync : Dispatch cfg thread (.sync resource) s (synchronize cfg s thread resource)

/-- No instruction is fetched while waiting. Wrong sites/resources cannot
release the barrier; requests are generated from actual fetched instructions. -/
def Step (cfg : Config n) (program : List Instr) (thread : Fin n)
    (s : State n) (out : Outcome n) : Prop :=
  s.barrier.arrived thread=false ∧
  ∃ i, program[(s.lanes thread).pc]?=some i ∧ Dispatch cfg thread i s out

inductive Runs (cfg : Config n) (program : List Instr) : State n → List (Event n) → State n → Prop where
  | nil : Runs cfg program s [] s
  | cons : Step cfg program thread s out → Runs cfg program out.state rest final →
      Runs cfg program s (out.events++rest) final

theorem waiting_blocks (waiting : s.barrier.arrived thread=true) : ¬Step cfg program thread s out := by
  intro h; have hf := h.1; simp [waiting] at hf

def Aligned (s : State n) : Prop :=
  ∀ t, s.barrier.arrived t=true → s.site=some (s.lanes t).pc

theorem setLane_aligned (aligned : Aligned s) (fresh : s.barrier.arrived thread=false)
    (lane : PTX.State) : Aligned (setLane s thread lane) := by
  intro t ht
  have different : t≠thread := by intro e; subst t; simp [setLane,fresh] at ht
  simpa [setLane,Function.update,different] using aligned t ht

theorem synchronize_aligned (cfg : Config n) (s : State n) (thread : Fin n) (resource : Fin 16)
    (aligned : Aligned s) : Aligned (synchronize cfg s thread resource).state := by
  unfold synchronize
  generalize hc : barrierConfig cfg s thread = c
  generalize hr : barrierRequest cfg s thread resource = r
  have requestThread : r.thread = thread := by subst r; rfl
  by_cases same : r.key = Ptx.Barrier.key c s.barrier
  · have siteEq : (s.lanes thread).pc = c.site := by
      have h := congrArg Ptx.Barrier.Key.site same
      simpa [← hr,barrierRequest,Ptx.Barrier.key] using h
    by_cases old : s.barrier.arrived r.thread = true
    · simp only [Ptx.Barrier.step,same,old,↓reduceIte]
      intro t ht
      have hs := aligned t ht
      have current := aligned thread (requestThread ▸ old)
      have eq : (s.lanes t).pc = (s.lanes thread).pc := Option.some.inj (hs.symm.trans current)
      simp [← siteEq,eq]
    · by_cases complete : Ptx.Barrier.Complete (Ptx.Barrier.mark s.barrier r.thread)
      · simp only [Ptx.Barrier.step,same,old,complete,↓reduceIte]
        intro t ht
        simp [Ptx.Barrier.reset] at ht
      · simp only [Ptx.Barrier.step,same,old,complete,↓reduceIte]
        intro t ht
        by_cases eq : t = thread
        · simp [eq,siteEq]
        · have previous : s.barrier.arrived t = true := by
            simpa [Ptx.Barrier.mark,requestThread,eq] using ht
          have hs := aligned t previous
          have cfgSite : c.site = (s.lanes t).pc := by
            rw [← hc]; simp [barrierConfig,hs]
          simp [cfgSite]
  · simpa only [Ptx.Barrier.step,same,↓reduceIte] using aligned


theorem step_aligned (step : Step cfg program thread s out) (aligned : Aligned s) : Aligned out.state := by
  obtain ⟨fresh,i,fetch,h⟩ := step
  cases h with
  | data => exact setLane_aligned aligned fresh _
  | skip => exact setLane_aligned aligned fresh _
  | sync => exact synchronize_aligned _ _ _ _ aligned

theorem runs_aligned (run : Runs cfg program s events final) (aligned : Aligned s) : Aligned final := by
  induction run with
  | nil => exact aligned
  | cons step _ ih => exact ih (step_aligned step aligned)

end PtxTorchLean.Poisson.PTX.Concurrent

import PoissonPTX.ConcurrentTail

namespace PtxTorchLean.Poisson.PTX.Relocate

def scalar (offset : Nat) (s : PTX.State) : PTX.State := {s with pc:=s.pc+offset}

@[simp] theorem scalar_pc : (scalar offset s).pc=s.pc+offset := rfl

@[simp] theorem scalar_regs : (scalar offset s).regs=s.regs := rfl

@[simp] theorem operand : Operand.eval (scalar offset s) op=Operand.eval s op := by
  cases op <;> rfl

@[simp] theorem scalar_advance : scalar offset (advance s)=advance (scalar offset s) := by
  simp [scalar,advance,Nat.add_right_comm]

@[simp] theorem scalar_assign : scalar offset (assign s r w)=assign (scalar offset s) r w := by
  simp [scalar,assign,advance,Nat.add_right_comm]

@[simp] theorem scalar_put : scalar offset (put s sp a w)=put (scalar offset s) sp a w := by
  cases sp <;> simp [scalar,put,advance,Nat.add_right_comm]

@[simp] theorem memory : (scalar offset s).memory sp=s.memory sp := by cases sp <;> rfl
@[simp] theorem start : (scalar offset s).start sp=s.start sp := by cases sp <;> rfl
@[simp] theorem bytes : (scalar offset s).bytes sp=s.bytes sp := by cases sp <;> rfl

/-- Arithmetic and memory effects commute with moving the instruction origin. -/
theorem eval (step : PTX.Eval op s t) : PTX.Eval op (scalar offset s) (scalar offset t) := by
  cases step with
  | mov => simpa using (PTX.Eval.mov (s:=scalar offset _) (dst:=_) (src:=_))
  | mul32 => simpa using (PTX.Eval.mul32 (s:=scalar offset _) (dst:=_) (a:=_) (b:=_))
  | add32 => simpa using (PTX.Eval.add32 (s:=scalar offset _) (dst:=_) (a:=_) (b:=_))
  | add64 => simpa using (PTX.Eval.add64 (s:=scalar offset _) (dst:=_) (a:=_) (b:=_))
  | wide8 => simpa using (PTX.Eval.wide8 (s:=scalar offset _) (dst:=_) (index:=_))
  | load64 valid =>
    simpa using (PTX.Eval.load64 (s:=scalar offset _) (dst:=_) (address:=_) (space:=_) (by simpa using valid))
  | store64 valid =>
    simpa using (PTX.Eval.store64 (s:=scalar offset _) (address:=_) (src:=_) (space:=_) (by simpa using valid))
  | fp allowed =>
    simpa using (PTX.Eval.fp (s:=scalar offset _) (dst:=_) (a:=_) (b:=_) (op:=_) (out:=_) (by simpa using allowed))


def access (offset : Nat) (a : Concurrent.Access) : Concurrent.Access :=
  {a with data:={a.data with pc:=a.data.pc+offset}}

def key (offset : Nat) (k : Ptx.Barrier.Key) : Ptx.Barrier.Key := {k with site:=k.site+offset}

def barrierEvent (offset : Nat) : Ptx.Barrier.Event n → Ptx.Barrier.Event n
  | .arrival k t => .arrival (key offset k) t
  | .completion k => .completion (key offset k)

def event (offset : Nat) : Concurrent.Event n → Concurrent.Event n
  | .data t a => .data t (access offset a)
  | .barrier e => .barrier (barrierEvent offset e)

def core (offset : Nat) (s : Concurrent.State n) : Concurrent.State n :=
  ⟨fun t => scalar offset (s.lanes t),s.barrier,s.site.map (·+offset)⟩

def outcome (offset : Nat) (s : Concurrent.Outcome n) : Concurrent.Outcome n :=
  ⟨core offset s.state,s.events.map (event offset)⟩

theorem key_injective : Function.Injective (key offset) := by
  intro a b h
  cases a; cases b
  simpa [key,Ptx.Barrier.Key.mk.injEq] using h

theorem data (step : Concurrent.Data op s t a) :
    Concurrent.Data op (scalar offset s) (scalar offset t) (a.map (access offset)) := by
  cases step with
  | ordinary plain he => simpa using Concurrent.Data.ordinary plain (eval (offset:=offset) he)
  | load valid =>
    simpa only [scalar_assign,Option.map_some,access,operand,scalar_pc] using (Concurrent.Data.load (s:=scalar offset _) (sp:=_) (dst:=_) (addr:=_) (word:=_)
      (by simpa using valid))
  | store valid =>
    simpa only [scalar_put,Option.map_some,access,operand,scalar_pc] using (Concurrent.Data.store (s:=scalar offset _) (sp:=_) (addr:=_) (src:=_)
      (by simpa using valid))

def barrierConfig (offset : Nat) (cfg : Ptx.Barrier.Config n) : Ptx.Barrier.Config n :=
  {cfg with site:=cfg.site+offset}

def request (offset : Nat) (r : Ptx.Barrier.Request n) : Ptx.Barrier.Request n :=
  {r with key:=key offset r.key}

def barrierResult (offset : Nat) (r : Ptx.Barrier.Result n) : Ptx.Barrier.Result n :=
  {r with events:=r.events.map (barrierEvent offset)}

theorem barrier_step (cfg : Ptx.Barrier.Config n) (s : Ptx.Barrier.State n) (r : Ptx.Barrier.Request n) :
    Ptx.Barrier.step (barrierConfig offset cfg) s (request offset r)=
      barrierResult offset (Ptx.Barrier.step cfg s r) := by
  have configKey : Ptx.Barrier.key (barrierConfig offset cfg) s=key offset (Ptx.Barrier.key cfg s) := rfl
  simp only [Ptx.Barrier.step,request,configKey,key_injective.eq_iff]
  by_cases same : r.key=Ptx.Barrier.key cfg s <;>
    by_cases old : s.arrived r.thread=true <;>
    by_cases complete : Ptx.Barrier.Complete (Ptx.Barrier.mark s r.thread) <;>
    simp [same,old,complete,barrierResult,barrierEvent]


@[simp] theorem core_lane : (core offset s).lanes t=scalar offset (s.lanes t) := rfl
@[simp] theorem core_barrier : (core offset s).barrier=s.barrier := rfl
@[simp] theorem core_site : (core offset s).site=s.site.map (·+offset) := rfl

@[simp] theorem core_setLane : core offset (Concurrent.setLane s t next)=
    Concurrent.setLane (core offset s) t (scalar offset next) := by
  simp only [core,Concurrent.setLane]
  congr 1
  funext u
  by_cases h : u=t <;> simp [Function.update,h]

@[simp] theorem shifted_config (cfg : Concurrent.Config n) (s : Concurrent.State n) (t : Fin n) :
    Concurrent.barrierConfig cfg (core offset s) t=barrierConfig offset (Concurrent.barrierConfig cfg s t) := by
  cases hs : s.site <;> simp [Concurrent.barrierConfig,core,barrierConfig,scalar,hs]

@[simp] theorem shifted_request (cfg : Concurrent.Config n) (s : Concurrent.State n) (t : Fin n) (r : Fin 16) :
    Concurrent.barrierRequest cfg (core offset s) t r=request offset (Concurrent.barrierRequest cfg s t r) := rfl

/-- The barrier protocol relocates its key site together with fetched counters. -/
theorem synchronize (cfg : Concurrent.Config n) (s : Concurrent.State n) (t : Fin n) (r : Fin 16) :
    Concurrent.synchronize cfg (core offset s) t r=outcome offset (Concurrent.synchronize cfg s t r) := by
  simp only [Concurrent.synchronize,shifted_config,shifted_request,barrier_step,barrierResult]
  generalize h : Ptx.Barrier.step (Concurrent.barrierConfig cfg s t) s.barrier
    (Concurrent.barrierRequest cfg s t r)=result
  cases hd : result.disposition <;> simp [outcome,core,hd,h,barrierConfig,scalar_advance,event,List.map_map,Function.comp_def]

/-- Absolute branch targets move with the segment. -/
def instruction (offset : Nat) : Concurrent.Instr → Concurrent.Instr
  | .skip active target => .skip active (target+offset)
  | i => i

theorem dispatch (step : Concurrent.Dispatch cfg t i s out) :
    Concurrent.Dispatch cfg t (instruction offset i) (core offset s) (outcome offset out) := by
  cases step with
  | data h =>
    simpa [instruction,outcome,event,List.map_map,Function.comp_def,Option.toList_map] using
      Concurrent.Dispatch.data (cfg:=cfg) (thread:=t) (s:=core offset s) (data (offset:=offset) h)
  | skip =>
    rename_i active target
    by_cases live : t.val<active
    all_goals simpa [instruction,outcome,core_setLane,core_lane,scalar,live,Nat.add_right_comm] using
      (Concurrent.Dispatch.skip (cfg:=cfg) (thread:=t) (s:=core offset s) (active:=active) (target:=target+offset))
  | sync =>
    simpa only [instruction,synchronize] using
      (Concurrent.Dispatch.sync (cfg:=cfg) (thread:=t) (s:=core offset _) (resource:=_))

end PtxTorchLean.Poisson.PTX.Relocate

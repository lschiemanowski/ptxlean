import PoissonPTX.CellEntryInputs

namespace PtxTorchLean.Poisson.PTX.CellEntry.Local

/-- Sequential projection of one lane. The sync case records that lane's
advance at an actual collective release; this is not a stand-alone barrier rule. -/
def eval (ctx : CellPrologue.Context) : Instr → CellPrologue.State → Option CellPrologue.State
  | .setup op,s => CellPrologue.eval ctx op s
  | .gather op,s => (Indexed.eval op s.core).map fun core => ⟨core,s.live⟩
  | .skip target,s => some ⟨{s.core with pc:=if s.live then s.core.pc+1 else target},s.live⟩
  | .sync,s => some ⟨advance s.core,s.live⟩

def Step (ctx : CellPrologue.Context) (code : List Instr) (s t : CellPrologue.State) : Prop :=
  ∃ i, code[s.core.pc]?=some i ∧ eval ctx i s=some t

inductive Runs (ctx : CellPrologue.Context) (code : List Instr) : CellPrologue.State → CellPrologue.State → Prop
  | nil : Runs ctx code s s
  | cons : Step ctx code s t → Runs ctx code t u → Runs ctx code s u

theorem trans (first : Runs ctx code s t) (second : Runs ctx code t u) : Runs ctx code s u := by
  induction first with
  | nil => exact second
  | cons step _ ih => exact .cons step (ih second)

theorem deterministic (a : Step ctx code s t) (b : Step ctx code s u) : t=u := by
  obtain ⟨i,fetch,step⟩ := a
  obtain ⟨j,fetch',step'⟩ := b
  have same := Option.some.inj (fetch.symm.trans fetch')
  subst j
  exact Option.some.inj (step.symm.trans step')

theorem terminal_unique (a : Runs ctx code s t) (b : Runs ctx code s u)
    (stopT : code[t.core.pc]?=none) (stopU : code[u.core.pc]?=none) : t=u := by
  induction a with
  | nil => cases b with
    | nil => rfl
    | cons step _ => obtain ⟨i,fetch,_⟩ := step; rw [stopT] at fetch; cases fetch
  | cons step rest ih => cases b with
    | nil => obtain ⟨i,fetch,_⟩ := step; rw [stopU] at fetch; cases fetch
    | cons step' rest' =>
      have same := deterministic step step'
      subst_vars
      exact ih rest' stopT

theorem prologue (run : CellPrologue.Runs ctx pre fuel s t) (suffix : List Instr) :
    Runs ctx (pre.map .setup++suffix) s t := by
  induction run with
  | nil => exact .nil
  | cons step rest ih =>
    obtain ⟨i,fetch,he⟩ := step
    apply Runs.cons ⟨.setup i,?_,he⟩ ih
    have bound := (List.getElem?_eq_some_iff.mp fetch).1
    rw [List.getElem?_append_left (by simpa using bound),List.getElem?_map,fetch]
    rfl

theorem gather (run : Indexed.Block ops s.core t) (plain : ∀ i∈ops, Indexed.noFP i=true)
    (pre suffix : List Instr) (pc : s.core.pc=pre.length) :
    Runs ctx (pre++ops.map .gather++suffix) s ⟨t,s.live⟩ := by
  generalize coreEq : s.core=core at run
  induction run generalizing s pre with
  | nil => cases s; simp only at coreEq; subst_vars; exact .nil
  | @cons i core mid rest final he run ih =>
    have executed := Indexed.eval_complete he (plain _ (by simp))
    have next : mid.pc=(pre++[Instr.gather i]).length := by
      rw [Indexed.eval_pc he,← coreEq,pc]; simp
    apply Runs.cons (t:=⟨mid,s.live⟩) ⟨.gather i,by simp [pc],?_⟩
      (by
        have glue : pre++(i::rest).map Instr.gather++suffix=
            (pre++[Instr.gather i])++rest.map Instr.gather++suffix := by simp [List.append_assoc]
        rw [glue]
        exact ih (fun i hi => plain i (by simp [hi])) (s:=⟨mid,s.live⟩) (pre:=pre++[Instr.gather i]) next rfl)
    simp [eval,coreEq,executed]

def beforeGather (ctx : CellPrologue.Context) (width : Nat) (s : CellPrologue.State) : PTX.State :=
  advance (CellPrologue.finish ctx width s).core

def finish (ctx : CellPrologue.Context) (width : Nat) (cells source : Word) (s : CellPrologue.State) : CellPrologue.State :=
  let setup := CellPrologue.finish ctx width s
  if setup.live then ⟨advance (CellGather.finish (beforeGather ctx width s) width cells source),setup.live⟩
  else ⟨{setup.core with pc:=21},setup.live⟩

/-- A complete local trace constructed from the already-proved prologue and
gather. The barrier step here must still be justified by a concurrent release. -/
theorem exists_trace (ctx : CellPrologue.Context) (s : CellPrologue.State) (pc : s.core.pc=0)
    (positive : 0<width) (fits : width*width<2^32)
    (valid : ctx.lane.toNat<width*width → CellGather.Valid (beforeGather ctx width s) width cells source) :
    Runs ctx (program width cells source) s (finish ctx width cells source s) := by
  let ready := CellPrologue.finish ctx width s
  have readyPC : ready.core.pc=7 := by simp [ready,CellPrologue.finish,pc]
  have first := prologue (CellPrologue.fetched_exists ctx s pc positive fits)
    ([.skip 20]++(CellGather.code width cells source).map .gather++[.sync])
  apply trans (by simpa [program,List.append_assoc] using first)
  have guard : (program width cells source)[ready.core.pc]?=some (.skip 20) := by
    simp [readyPC,program,CellPrologue.program]
  by_cases live : ready.live=true
  · have active : ctx.lane.toNat<width*width := by simpa [ready,CellPrologue.finish] using live
    let body : CellPrologue.State := ⟨beforeGather ctx width s,ready.live⟩
    have prePC : body.core.pc=8 := by simp [body,beforeGather,advance,CellPrologue.finish,pc]
    apply Runs.cons ⟨.skip 20,guard,?_⟩
    · have gathered := gather (ctx:=ctx) (s:=body) (Indexed.run_sound (CellGather.execution (valid active)))
        (by simp [CellGather.code,Indexed.noFP,PTX.noFP])
        ((CellPrologue.program width).map .setup++[.skip 20]) [.sync]
        (by simpa [CellPrologue.program] using prePC)
      apply trans (by simpa [program] using gathered)
      apply Runs.cons ⟨.sync,?_,?_⟩ Runs.nil
      · change (program width cells source)[body.core.pc+12]?=some .sync
        rw [prePC]
        exact barrier_fetch
      · simp [eval,finish,ready,live,body]
    · simp [eval,live,body,beforeGather,ready,advance]
  · have inactive : ready.live=false := Bool.eq_false_iff.mpr live
    apply Runs.cons ⟨.skip 20,guard,rfl⟩
    apply Runs.cons ⟨.sync,?_,?_⟩ Runs.nil
    · simpa [eval,inactive] using (barrier_fetch (width:=width) (cells:=cells) (source:=source))
    · simp [eval,finish,ready,inactive,advance]

end PtxTorchLean.Poisson.PTX.CellEntry.Local

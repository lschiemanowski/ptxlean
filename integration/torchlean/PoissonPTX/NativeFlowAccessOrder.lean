import PoissonPTX.NativeFlowRegion
import PoissonPTX.NativeFlowOrigins
import PoissonPTX.ReductionSources

namespace PtxTorchLean.Poisson.PTX.Concurrent.NativeFlow

variable {n : Nat} {cfg : Config n} {ctx : Fin n → Kernel.Context}
  {start final s : State n} {out : Outcome n} {events : List (Event n)}
  {a b : Access} {i j : Nat}

/-- A loop may revisit the prefix below `cut`. Once an instruction reaches the
suffix, every explicit jump preserves the instruction rank. -/
def ForwardFrom (program : List Instr) (cut : Nat) : Prop :=
  ∀ pc i, program[pc]?=some (.flow i) → targets (fun target => max cut pc≤max cut target) i

theorem eval_rank {ctx : Kernel.Context} {s t : Flow.State} {i : Flow.Instr} (actual : Flow.Observed.Eval ctx i s t access index)
    (jumps : targets (fun target => max cut s.core.pc≤max cut target) i) :
    max cut s.core.pc≤max cut t.core.pc := by
  cases actual with
  | data step => rw [Indexed.Candidate.data_pc step]; omega
  | simple ordinary =>
    cases i <;> simp_all [targets,Flow.simple,Flow.next,Flow.goto,Flow.halt,assign,advance]
    all_goals first | omega | (split <;> simp_all <;> omega)

theorem step_rank (actual : Step cfg ctx program selected s out)
    (forward : ForwardFrom program cut) (owner : Fin n) :
    max cut (s.core.lanes owner).pc≤max cut (out.state.core.lanes owner).pc := by
  cases actual with
  | flow running fresh fetch effect =>
    by_cases same : owner=selected
    · subst owner
      have bound := eval_rank effect (forward _ _ fetch)
      simpa only [update,setLane,Function.update_self,lane] using bound
    · simp [update,setLane,Function.update,same]
  | @sync _ resource running fresh fetch => exact max_le_max_left cut (sync_monotone s cfg selected owner resource)

theorem runs_rank (actual : Runs cfg ctx program start events indices final)
    (forward : ForwardFrom program cut) (owner : Fin n) :
    max cut (start.core.lanes owner).pc≤max cut (final.core.lanes owner).pc := by
  induction actual with
  | nil => rfl
  | cons step rest ih => exact (step_rank step forward owner).trans ih

theorem eval_access_pc {ctx : Kernel.Context} {s t : Flow.State} {i : Flow.Instr} (actual : Flow.Observed.Eval ctx i s t (some access) index) :
    access.data.pc=s.core.pc ∧ t.core.pc=access.data.pc+1 := by
  cases actual with
  | data step =>
    cases step with
    | data step => exact ⟨Concurrent.access_pc step,by rw [Concurrent.data_pc step,Concurrent.access_pc step]⟩

theorem access_single (actual : Step cfg ctx program selected s out)
    (member : Event.data owner access∈out.events) : out.events=[.data owner access] := by
  cases actual with
  | flow running fresh fetch effect =>
    cases ‹Option Access› <;> simp_all
  | sync => simp only [synchronize] at member; split at member <;> simp_all

theorem access_post (actual : Step cfg ctx program selected s out)
    (member : Event.data owner access∈out.events) :
    (out.state.core.lanes owner).pc=access.data.pc+1 := by
  cases actual with
  | flow running fresh fetch effect =>
    cases h : ‹Option Access› with
    | none => simp [h] at member
    | some a =>
      simp only [h,Option.toList_some,List.map_cons,List.map_nil,List.mem_singleton,Event.data.injEq] at member
      obtain ⟨rfl,rfl⟩ := member
      have post := (eval_access_pc (h ▸ effect)).2
      simpa only [update,setLane,Function.update_self] using post
  | sync => simp only [synchronize] at member; split at member <;> simp_all

theorem access_rank_bound (actual : Runs cfg ctx program start events indices final)
    (forward : ForwardFrom program cut) (member : Event.data owner access∈events) :
    max cut (start.core.lanes owner).pc≤max cut access.data.pc := by
  obtain ⟨before,earlier,earlierIndices,selected,out,run,step,found⟩ := access_prefix actual member
  obtain ⟨rfl,i,next,index,fetch,effect⟩ := step_access_origin step found
  rw [(eval_access_pc effect).1]
  exact runs_rank run forward owner

def SuffixAccessOrder (cut : Nat) (left right : Event n) : Prop :=
  ∀ owner a b, left=.data owner a → right=.data owner b → cut≤a.data.pc → a.data.pc<b.data.pc

/-- Strict occurrence order holds for suffix accesses even though the earlier
input loop can revisit its loads arbitrarily many times. -/
theorem access_order (actual : Runs cfg ctx program start events indices final)
    (forward : ForwardFrom program cut) : events.Pairwise (SuffixAccessOrder cut) := by
  induction actual with
  | nil => simp
  | cons step rest ih =>
    apply List.pairwise_append.mpr
    refine ⟨?_,ih,?_⟩
    · apply List.pairwise_iff_getElem.mpr
      intro i j hi hj hij owner a b left right suffix
      have member : Event.data owner a∈_ := left ▸ List.getElem_mem hi
      have single := access_single step member
      have size := congrArg List.length single
      simp only [List.length_singleton] at size
      omega
    · intro left hl right hr owner a b sameLeft sameRight suffix
      subst left; subst right
      have post := access_post step hl
      have bound := access_rank_bound rest forward hr
      rw [post] at bound
      omega

theorem access_unique (actual : Runs cfg ctx program start events indices final)
    (forward : ForwardFrom program cut)
    (left : events[i]?=some (.data owner a)) (right : events[j]?=some (.data owner b))
    (suffix : cut≤a.data.pc) (same : a.data.pc=b.data.pc) : i=j := by
  obtain ⟨hi,he⟩ := List.getElem?_eq_some_iff.mp left
  obtain ⟨hj,hf⟩ := List.getElem?_eq_some_iff.mp right
  have ordered := access_order actual forward
  rcases lt_trichotomy i j with lt | eq | gt
  · have h := ordered.rel_getElem_of_lt hi hj lt owner a b he hf suffix; omega
  · exact eq
  · have h := ordered.rel_getElem_of_lt hj hi gt owner b a hf he (by omega); omega

/-- Instruction order in the suffix derives a same-thread causal edge. It
never infers cross-thread causality from chronological event-list order. -/
theorem before_of_pc (actual : Runs cfg ctx program start events indices final)
    (forward : ForwardFrom program cut)
    (left : events[i]?=some (.data owner a)) (right : events[j]?=some (.data owner b))
    (suffix : cut≤a.data.pc) (pc : a.data.pc<b.data.pc) : Visibility.Repeated.Before events i j := by
  obtain ⟨hi,he⟩ := List.getElem?_eq_some_iff.mp left
  obtain ⟨hj,hf⟩ := List.getElem?_eq_some_iff.mp right
  have ordered := access_order actual forward
  have lt : i<j := by
    rcases lt_trichotomy i j with lt | eq | gt
    · exact lt
    · subst j
      have same := Option.some.inj (left.symm.trans right)
      cases same
      omega
    · have h := ordered.rel_getElem_of_lt hj hi gt owner b a hf he (by omega); omega
  exact .edge (.inl ⟨owner,a,b,left,right,lt⟩)

end PtxTorchLean.Poisson.PTX.Concurrent.NativeFlow

import PoissonPTX.RepeatedShared
import PoissonPTX.ConcurrentExec

namespace PtxTorchLean.Poisson.PTX.Concurrent.Visibility.Repeated.Checks

/-- Small actual single-participant block, solely a memory-rule regression;
it is not the emitted 256-thread reduction. -/
def program : List Instr := [
  .data (.store64 .shared (.imm 0) (.imm 3)),.sync 0,
  .data (.store64 .shared (.imm 0) (.imm 7)),.sync 0,
  .data (.load64 .shared 0 (.imm 0)),
  .data (.store64 .shared (.imm 0) (.imm 9))]

def start : Concurrent.State 1 := ⟨fun _ =>
  ⟨0,fun _ => 0,fun _ => 0,fun _ => 0,0,0,0,8⟩,Ptx.Barrier.reset 0,none⟩
def cfg : Config 1 := ⟨0,by decide⟩
def execution (value : Word) := execute cfg program (fun _ _ => value) (List.replicate 6 0) start
def result (value : Word) : Outcome 1 := (execution value).getD ⟨start,[]⟩
def history (value : Word) : List (Event 1) := [
  .data 0 ⟨.shared,⟨0,true,0,3⟩⟩,
  .barrier (.arrival ⟨0,0,0,1⟩ 0),.barrier (.completion ⟨0,0,0,1⟩),
  .data 0 ⟨.shared,⟨2,true,0,7⟩⟩,
  .barrier (.arrival ⟨0,0,1,3⟩ 0),.barrier (.completion ⟨0,0,1,3⟩),
  .data 0 ⟨.shared,⟨4,false,0,value⟩⟩,
  .data 0 ⟨.shared,⟨5,true,0,9⟩⟩]

def source (writer : Nat) : Nat → Fin 8 → Sources.Origin Nat := fun _ k => .store writer k

theorem executed (value : Word) : execution value=some (result value) ∧ (result value).events=history value := by
  constructor <;> rfl


theorem actual (value : Word) : Runs cfg program start (history value) (result value).state := by
  have run := execute_sound (executed value).1
  simpa only [(executed value).2] using run

theorem read_index (observed : (history value)[r]?=some (.data reader access))
    (read : access.data.store=false) : r=6 := by
  have bound : r<8 := (List.getElem?_eq_some_iff.mp observed).1
  interval_cases r <;> simp [history] at observed <;> obtain ⟨rfl,rfl⟩ := observed
  all_goals simp_all

theorem store_index (observed : (history value)[w]?=some (.data writer access))
    (store : access.data.store=true) : w=0 ∨ w=3 ∨ w=7 := by
  have bound : w<8 := (List.getElem?_eq_some_iff.mp observed).1
  interval_cases w <;> simp [history] at observed <;> obtain ⟨rfl,rfl⟩ := observed
  all_goals simp_all

/-- Initialization exclusion alone cannot distinguish actual old and new stores. -/
theorem old_constraints (value : Word) (w : Nat) (observed :
    (history value)[w]?=some (.data 0 ⟨.shared,⟨pc,true,0,value⟩⟩)) :
    Compatible (fun _ _ => 0) (history value) (source w) ∧ Performed (history value) (source w) := by
  constructor
  · intro r reader ra hr read k
    have eq := read_index hr read
    subst r
    simp [history] at hr
    obtain ⟨rfl,rfl⟩ := hr
    exact ⟨0,⟨.shared,⟨pc,true,0,value⟩⟩,observed,rfl,rfl,rfl,rfl⟩
  · intro w' r writer reader wa ra hw hr store read sw sr before j k address
    simp [source]

theorem obsolete_passes_old : Compatible (fun _ _ => 0) (history 3) (source 0) ∧
    Performed (history 3) (source 0) := old_constraints 3 0 (pc:=0) rfl

theorem future_passes_old : Compatible (fun _ _ => 0) (history 9) (source 7) ∧
    Performed (history 9) (source 7) := old_constraints 9 7 (pc:=5) rfl

theorem newest_compatible : Compatible (fun _ _ => 0) (history 7) (source 3) :=
  (old_constraints 7 3 (pc:=2) rfl).1

theorem thread_before (a b : Nat) (ha : (history value)[a]?=some (.data 0 left))
    (hb : (history value)[b]?=some (.data 0 right)) (lt : a<b) : Before (history value) a b :=
  .edge (.inl ⟨0,left,right,ha,hb,lt⟩)

/-- A causally later write cannot explain an earlier load's result. -/
theorem future_rejected : ¬OrderedSources (history 9) (source 7) := by
  intro h
  obtain ⟨coherence,ordered,future,stale⟩ := h.ordered
  exact future 6 7 0 0 ⟨.shared,⟨4,false,0,9⟩⟩ ⟨.shared,⟨5,true,0,9⟩⟩
    rfl rfl rfl rfl rfl rfl (thread_before 6 7 rfl rfl (by decide)) 0 0 rfl rfl

/-- Existence of a more recent performed store excludes the obsolete source. -/
theorem obsolete_rejected : ¬OrderedSources (history 3) (source 0) := by
  intro h
  obtain ⟨coherence,ordered,future,stale⟩ := h.ordered
  have co := ordered 0 3 0 0 ⟨.shared,⟨0,true,0,3⟩⟩ ⟨.shared,⟨2,true,0,7⟩⟩
    rfl rfl rfl rfl rfl rfl (thread_before 0 3 rfl rfl (by decide)) 0 0 rfl
  have noOld := stale 3 6 0 0 ⟨.shared,⟨2,true,0,7⟩⟩ ⟨.shared,⟨4,false,0,3⟩⟩
    rfl rfl rfl rfl rfl rfl (thread_before 3 6 rfl rfl (by decide)) 0 0 rfl
  exact noOld co

/-- The extension is inhabited by the actual new value, with chronological
coherence as one possible witness for this sequential test execution. -/
theorem newest_admissible : OrderedSources (history 7) (source 3) := by
  refine ⟨Nat.lt,?_,?_,?_⟩
  · intro a b left right la ra ha hb ls rs lsp rsp before j k address
    exact before_lt before
  · intro r w reader writer ra wa hr hw read store rs ws before j k address
    have eq := read_index hr read
    have lt := before_lt before
    intro equal
    have same : 3=w := (Sources.Origin.store.inj equal).1
    omega
  · intro w r writer reader wa ra hw hr store read ws rs before j k address
    have eq := read_index hr read
    have lt := before_lt before
    have options := store_index hw store
    change ¬3<w
    omega

/-- Every allowed source is forced to the stage write, independently of its
proposed load bits. This is stronger than checking the example value seven. -/
theorem forced_stage (compatible : Compatible initial (history value) choices)
    (admitted : OrderedSources (history value) choices) : value=7 ∧ ∀ k, choices 6 k=.store 3 k := by
  apply read_from_stage compatible admitted (w:=3) (r:=6) (writer:=0) (reader:=0)
    (wa:=⟨.shared,⟨2,true,0,7⟩⟩) (ra:=⟨.shared,⟨4,false,0,value⟩⟩)
    rfl rfl rfl rfl rfl rfl rfl (thread_before 3 6 rfl rfl (by decide))
  intro other thread access found store shared j k address
  rcases store_index found store with zero | current | last
  · right; left; subst other; exact thread_before 0 3 rfl rfl (by decide)
  · exact .inl current
  · right; right; subst other; exact thread_before 6 7 rfl rfl (by decide)

end PtxTorchLean.Poisson.PTX.Concurrent.Visibility.Repeated.Checks

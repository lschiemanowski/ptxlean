import PtxBinary32.GridConcrete
import PtxBinary32.ParallelReplaySources

/-! Checked replay preserves one global array and each group's private scratch.
It validates concrete read values before the separate graph admission proof. -/
namespace Ptx.Scalar.Parallel.Grid.Replay
structure Arrays (groups : Nat) where
  global : List Word
  shared : Fin groups → List Word

def arrays (s : Grid.State groups n) : Arrays groups := ⟨s.global,fun g => (s.blocks g).shared⟩
def view (s : Arrays groups) (g : Fin groups) : Parallel.Replay.Arrays := ⟨s.global,s.shared g⟩
def install (s : Arrays groups) (g : Fin groups) (next : Parallel.Replay.Arrays) : Arrays groups :=
  ⟨next.global,Function.update s.shared g next.shared⟩
def arena (s : Arrays groups) (g : Fin groups) : Space → List Word
  | .global => s.global | .shared => s.shared g

def event (s : Arrays groups) (e : Grid.Event groups n) : Option (Arrays groups) :=
  (Parallel.Replay.event (view s e.1) e.2).map (install s e.1)
def trace (s : Arrays groups) : List (Grid.Event groups n) → Option (Arrays groups)
  | [] => some s
  | e::es => (event s e).bind (fun next => trace next es)

theorem trace_append (s : Arrays groups) (left right : List (Grid.Event groups n)) :
    trace s (left++right)=(trace s left).bind (fun middle => trace middle right) := by
  induction left generalizing s with
  | nil => rfl
  | cons e es ih => simp [trace,ih,Option.bind_assoc]

theorem trace_tag (s : Arrays groups) (g : Fin groups) (events : List (Parallel.Event n)) :
    trace s (Grid.tag g events)=
      (Parallel.Replay.trace (view s g) events).map (install s g) := by
  induction events generalizing s with
  | nil => simp [trace,Grid.tag,Parallel.Replay.trace,install,view]
  | cons e es ih =>
    simp only [Grid.tag,List.map_cons,trace,event]
    cases h : Parallel.Replay.event (view s g) e with
    | none => simp [h,Parallel.Replay.trace]
    | some next =>
      simp only [h,Option.map_some,Option.bind_some]
      rw [show List.map (fun e => (g,e)) es=Grid.tag g es from rfl,ih]
      have same : view (install s g next) g=next := by simp [view,install]
      rw [same,Parallel.Replay.trace,h]
      simp only [Option.bind_some]
      congr 1
      funext result
      simp [install,Function.update_idem]

theorem arrays_install (s : Grid.State groups n) (g : Fin groups) (next : Parallel.State n) :
    arrays (Grid.install s g next)=install (arrays s) g (Parallel.Replay.arrays next) := by
  unfold arrays Grid.install install Parallel.Replay.arrays
  congr 1
  funext h
  by_cases same : h=g
  · subst h; simp [Grid.localOf]
  · simp [same]

theorem concrete_replays {s final : Grid.State groups n} {events : List (Grid.Event groups n)}
    (run : Grid.ConcreteRuns cfg program s events final) : trace (arrays s) events=some (arrays final) := by
  induction run with
  | nil => rfl
  | cons g t out step _ ih =>
    rw [trace_append,trace_tag]
    have checked := Parallel.Replay.step_replays step
    change Parallel.Replay.trace (view (arrays _) g) _=some (Parallel.Replay.arrays out.state) at checked
    rw [checked]
    simpa only [Option.map_some,Option.bind_some,arrays_install] using ih

def writtenAt (g : Fin groups) (space : Space) (index : Nat) (e : Grid.Event groups n) : Option Word :=
  if space=.global ∨ e.1=g then Parallel.Replay.writtenAt space index e.2 else none

def latestWrite (g : Fin groups) (space : Space) (index : Nat) : List (Grid.Event groups n) → Option Word
  | [] => none
  | e::es => (latestWrite g space index es).or (writtenAt g space index e)

theorem latestWrite_none (g : Fin groups) (space : Space) (index : Nat) (events : List (Grid.Event groups n)) :
    latestWrite g space index events=none ↔ ∀ e ∈ events, writtenAt g space index e=none := by
  induction events with
  | nil => simp [latestWrite]
  | cons e es ih => simp [latestWrite,Option.or_eq_none_iff,ih,and_comm]

theorem latestWrite_origin (g : Fin groups) (space : Space) (index : Nat)
    (events : List (Grid.Event groups n)) (value : Word) (found : latestWrite g space index events=some value) :
    ∃ before e after, events=before++e::after ∧ writtenAt g space index e=some value ∧
      ∀ later ∈ after, writtenAt g space index later=none := by
  induction events with
  | nil => simp [latestWrite] at found
  | cons e es ih =>
    cases h : latestWrite g space index es with
    | none => exact ⟨[],e,es,rfl,by simpa [latestWrite,h] using found,(latestWrite_none _ _ _ _).mp h⟩
    | some word =>
      have eq : word=value := by simpa [latestWrite,h] using found
      subst word
      obtain ⟨before,e',after,split,write,last⟩ := ih h
      exact ⟨e::before,e',after,by simp [split],write,last⟩

theorem event_value (s next : Arrays groups) (e : Grid.Event groups n)
    (checked : event s e=some next) (g : Fin groups) (space : Space) (index : Nat) :
    (arena next g space)[index]?=(writtenAt g space index e).or ((arena s g space)[index]?) := by
  obtain ⟨words,check,eq⟩ := Option.map_eq_some_iff.mp checked
  subst next
  have value := Parallel.Replay.event_value (view s e.1) words e.2 check space index
  cases space with
  | global => simpa [arena,writtenAt,install,view,Parallel.Replay.arena] using value
  | shared =>
    by_cases same : e.1=g
    · subst g; simpa [arena,writtenAt,install,view,Parallel.Replay.arena] using value
    · simp [arena,writtenAt,install,same,Ne.symm same]

theorem trace_value (s next : Arrays groups) (events : List (Grid.Event groups n))
    (checked : trace s events=some next) (g : Fin groups) (space : Space) (index : Nat) :
    (arena next g space)[index]?=(latestWrite g space index events).or ((arena s g space)[index]?) := by
  induction events generalizing s with
  | nil => cases Option.some.inj checked; rfl
  | cons e es ih =>
    obtain ⟨middle,step,tail⟩ := Option.bind_eq_some_iff.mp checked
    rw [ih middle tail,event_value s middle e step g space index]
    simp [latestWrite,Option.or_assoc]

theorem load_prefix (s final : Arrays groups) (before after : List (Grid.Event groups n))
    (g : Fin groups) (t : Fin n) (space : Space) (occ : Scalar.Occurrence) (address : Address) (value : Word)
    (load : occ.memory=some ⟨.load,address,value⟩)
    (checked : trace s (before++(g,.scalar t (some space) occ)::after)=some final) :
    ∃ middle, trace s before=some middle ∧ (arena middle g space)[address.toNat/4]?=some value := by
  rw [trace_append] at checked
  obtain ⟨middle,pre,tail⟩ := Option.bind_eq_some_iff.mp checked
  obtain ⟨next,step,_⟩ := Option.bind_eq_some_iff.mp tail
  obtain ⟨words,result,_⟩ := Option.map_eq_some_iff.mp step
  have one : Parallel.Replay.trace (view middle g) [.scalar t (some space) occ]=some words := by
    simp [Parallel.Replay.trace,result]
  obtain ⟨current,empty,_,read⟩ := Parallel.Replay.load_prefix (view middle g) words [] [] t space occ address value load one
  have eq : current=view middle g := (Option.some.inj empty).symm
  subst current
  exact ⟨middle,pre,by cases space <;> exact read⟩

theorem load_source (s final : Arrays groups) (before after : List (Grid.Event groups n))
    (g : Fin groups) (t : Fin n) (space : Space) (occ : Scalar.Occurrence) (address : Address) (value : Word)
    (load : occ.memory=some ⟨.load,address,value⟩)
    (checked : trace s (before++(g,.scalar t (some space) occ)::after)=some final) :
    ((arena s g space)[address.toNat/4]?=some value ∧ ∀ e ∈ before, writtenAt g space (address.toNat/4) e=none) ∨
    (∃ pre writer suffix, before=pre++writer::suffix ∧ writtenAt g space (address.toNat/4) writer=some value ∧
      ∀ e ∈ suffix, writtenAt g space (address.toNat/4) e=none) := by
  obtain ⟨middle,pre,read⟩ := load_prefix s final before after g t space occ address value load checked
  have values := trace_value s middle before pre g space (address.toNat/4)
  rw [read] at values
  cases found : latestWrite g space (address.toNat/4) before with
  | none => exact .inl ⟨by simpa [found] using values.symm,(latestWrite_none _ _ _ _).mp found⟩
  | some word =>
    have equal : word=value := by simpa [found] using values.symm
    subst word
    exact .inr (latestWrite_origin _ _ _ _ _ found)

theorem writtenAt_some (g : Fin groups) (space : Space) (index : Nat) (e : Grid.Event groups n) (value : Word)
    (write : writtenAt g space index e=some value) :
    ∃ h t occ address, e=(h,.scalar t (some space) occ) ∧ occ.memory=some ⟨.store,address,value⟩ ∧
      address.toNat/4=index ∧ (space=.global ∨ h=g) := by
  unfold writtenAt at write
  split at write
  · rename_i same
    obtain ⟨t,occ,address,eq,mem,word⟩ := Parallel.Replay.writtenAt_some _ _ _ _ write
    exact ⟨e.1,t,occ,address,Prod.ext rfl eq,mem,word,same⟩
  · contradiction
end Ptx.Scalar.Parallel.Grid.Replay

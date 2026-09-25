import PtxBinary32.ParallelReplay

/-! Read origins in a checked chronological replay. The latest preceding store
is identified in the actual event list; graph indexing and memory-order
admission remain separate obligations. -/
namespace Ptx.Scalar.Parallel.Replay

def arena (memory : Arrays) : Space → List Word
  | .global => memory.global | .shared => memory.shared

/-- The word written by this event to a particular space and word index. -/
def writtenAt (space : Space) (index : Nat) : Event n → Option Word
  | .scalar _ (some seen) occ => match occ.memory with
    | some e => if seen = space ∧ e.kind = .store ∧ e.address.toNat/4 = index then some e.value else none
    | none => none
  | _ => none

/-- Scan from the end: a later store takes precedence over every earlier one. -/
def latestWrite (space : Space) (index : Nat) : List (Event n) → Option Word
  | [] => none
  | e::es => (latestWrite space index es).or (writtenAt space index e)

theorem latestWrite_none (space : Space) (index : Nat) (events : List (Event n)) :
    latestWrite space index events = none ↔ ∀ e ∈ events, writtenAt space index e = none := by
  induction events with
  | nil => simp [latestWrite]
  | cons e es ih => simp [latestWrite,Option.or_eq_none_iff,ih,and_comm]

theorem latestWrite_origin (space : Space) (index : Nat) (events : List (Event n)) (value : Word)
    (found : latestWrite space index events = some value) :
    ∃ before e after, events = before++e::after ∧ writtenAt space index e = some value ∧
      ∀ later ∈ after, writtenAt space index later = none := by
  induction events with
  | nil => simp [latestWrite] at found
  | cons e es ih =>
    cases h : latestWrite space index es with
    | none =>
      exact ⟨[],e,es,rfl,by simpa [latestWrite,h] using found,(latestWrite_none _ _ _).mp h⟩
    | some word =>
      have eq : word=value := by simpa [latestWrite,h] using found
      subst word
      obtain ⟨before,e',after,split,write,last⟩ := ih h
      exact ⟨e::before,e',after,by simp [split],write,last⟩

private theorem effect_value (memory next : List Word) (e : Scalar.MemoryEffect)
    (checked : effect memory (some e) = some next) (index : Nat) :
    next[index]? = if e.kind = .store ∧ e.address.toNat/4 = index then some e.value else memory[index]? := by
  unfold effect at checked
  cases h : Scalar.addressIndex memory e.address with
  | error fault => simp [h] at checked
  | ok addrIndex =>
    have bound := (Scalar.addressIndex_ok_iff.mp h).1.2
    have eq := (Scalar.addressIndex_ok_iff.mp h).2
    subst addrIndex
    cases kind : e.kind with
    | load =>
      simp only [h,kind] at checked
      split at checked
      · cases Option.some.inj checked; simp
      · contradiction
    | store =>
      simp only [h,kind,Option.some.injEq] at checked
      subst next
      by_cases same : e.address.toNat/4=index
      · subst index; simp [bound]
      · simp [List.getElem?_set_ne same,same]

theorem event_value (memory next : Arrays) (e : Event n)
    (checked : event memory e = some next) (space : Space) (index : Nat) :
    (arena next space)[index]? = (writtenAt space index e).or ((arena memory space)[index]?) := by
  cases e with
  | scalar t seen occ =>
    cases seen with
    | none =>
      simp only [event] at checked
      split at checked
      · cases Option.some.inj checked; simp [writtenAt]
      · contradiction
    | some seen =>
      cases hm : occ.memory with
      | none =>
        cases seen <;> simp [event,hm,effect] at checked <;> subst next <;> simp [writtenAt,hm]
      | some eff =>
        cases seen <;> simp only [event,hm] at checked
        all_goals
          obtain ⟨words,result,equal⟩ := Option.map_eq_some_iff.mp checked
          subst next
          have value := effect_value _ _ eff result index
          cases space <;> simp [arena,writtenAt,hm,value]
          all_goals split <;> simp_all
  | binary32 t occ => cases Option.some.inj checked; rfl
  | barrier e => cases Option.some.inj checked; rfl
  | exit t pc => cases Option.some.inj checked; rfl

theorem trace_value (memory next : Arrays) (events : List (Event n))
    (checked : trace memory events = some next) (space : Space) (index : Nat) :
    (arena next space)[index]? = (latestWrite space index events).or ((arena memory space)[index]?) := by
  induction events generalizing memory with
  | nil => cases Option.some.inj checked; rfl
  | cons e es ih =>
    cases step : event memory e with
    | none => simp [trace,step] at checked
    | some middle =>
      simp only [trace,step,Option.bind_some] at checked
      rw [ih middle checked,event_value memory middle e step space index]
      simp only [latestWrite,Option.or_assoc]

private theorem effect_load (memory next : List Word) (address : Address) (value : Word)
    (checked : effect memory (some ⟨.load,address,value⟩) = some next) :
    Scalar.ValidAddress memory address ∧ memory[address.toNat/4]? = some value := by
  cases h : Scalar.addressIndex memory address with
  | error fault => simp [effect,h] at checked
  | ok index =>
    have valid := (Scalar.addressIndex_ok_iff.mp h).1
    have eq := (Scalar.addressIndex_ok_iff.mp h).2
    subst index
    simp only [effect,h] at checked
    split at checked
    · rename_i valueEq
      refine ⟨valid,?_⟩
      simpa only [List.getElem!_eq_getElem?_getD,List.getElem?_eq_getElem valid.2,
        Option.getD_some,Option.some.injEq] using valueEq
    · contradiction

/-- Extract the checked memory immediately before an actual load occurrence. -/
theorem load_prefix (memory final : Arrays) (before after : List (Event n))
    (t : Fin n) (space : Space) (occ : Scalar.Occurrence) (address : Address) (value : Word)
    (load : occ.memory = some ⟨.load,address,value⟩)
    (checked : trace memory (before++.scalar t (some space) occ::after) = some final) :
    ∃ middle, trace memory before = some middle ∧ Scalar.ValidAddress (arena middle space) address ∧
      (arena middle space)[address.toNat/4]? = some value := by
  rw [trace_append] at checked
  obtain ⟨middle,pre,tail⟩ := Option.bind_eq_some_iff.mp checked
  obtain ⟨next,step,_⟩ := Option.bind_eq_some_iff.mp tail
  refine ⟨middle,pre,?_⟩
  cases space <;> simp only [event,load] at step
  all_goals
    obtain ⟨words,result,_⟩ := Option.map_eq_some_iff.mp step
    exact effect_load _ _ address value result

/-- Each checked load uses either its initial word, with no preceding store to
that location, or the last preceding store in the actual trace. -/
theorem load_source (memory final : Arrays) (before after : List (Event n))
    (t : Fin n) (space : Space) (occ : Scalar.Occurrence) (address : Address) (value : Word)
    (load : occ.memory = some ⟨.load,address,value⟩)
    (checked : trace memory (before++.scalar t (some space) occ::after) = some final) :
    ((arena memory space)[address.toNat/4]? = some value ∧
      ∀ e ∈ before, writtenAt space (address.toNat/4) e = none) ∨
    (∃ pre writer suffix, before = pre++writer::suffix ∧
      writtenAt space (address.toNat/4) writer = some value ∧
      ∀ e ∈ suffix, writtenAt space (address.toNat/4) e = none) := by
  obtain ⟨middle,pre,_,read⟩ := load_prefix memory final before after t space occ address value load checked
  have values := trace_value memory middle before pre space (address.toNat/4)
  rw [read] at values
  cases found : latestWrite space (address.toNat/4) before with
  | none =>
    exact .inl ⟨by simpa [found] using values.symm,(latestWrite_none _ _ _).mp found⟩
  | some word =>
    have equal : word=value := by simpa [found] using values.symm
    subst word
    exact .inr (latestWrite_origin _ _ _ _ found)

/-- Origin information for every load, indexed by its actual trace split. -/
def ReadOrigins (memory : Arrays) (events : List (Event n)) : Prop :=
  ∀ (before after : List (Event n)) (t : Fin n) (space : Space) (occ : Scalar.Occurrence)
    (address : Address) (value : Word),
    events = before++.scalar t (some space) occ::after →
    occ.memory = some ⟨.load,address,value⟩ →
    ((arena memory space)[address.toNat/4]? = some value ∧
      ∀ e ∈ before, writtenAt space (address.toNat/4) e = none) ∨
    (∃ pre writer suffix, before = pre++writer::suffix ∧
      writtenAt space (address.toNat/4) writer = some value ∧
      ∀ e ∈ suffix, writtenAt space (address.toNat/4) e = none)

theorem read_origins (checked : trace memory events = some final) : ReadOrigins memory events := by
  intro before after t space occ address value split load
  subst events
  exact load_source memory final before after t space occ address value load checked

/-- A reported store really is a scalar store to the requested space and index. -/
theorem writtenAt_some (space : Space) (index : Nat) (e : Event n) (value : Word)
    (write : writtenAt space index e = some value) :
    ∃ t occ address, e = .scalar t (some space) occ ∧
      occ.memory = some ⟨.store,address,value⟩ ∧ address.toNat/4 = index := by
  cases e with
  | scalar t seen occ =>
    cases seen with
    | none => simp [writtenAt] at write
    | some seen =>
      cases hm : occ.memory with
      | none => simp [writtenAt,hm] at write
      | some eff =>
        simp only [writtenAt,hm] at write
        split at write
        · rename_i good
          obtain ⟨rfl,kind,addr⟩ := good
          have val := Option.some.inj write
          refine ⟨t,occ,eff.address,rfl,?_,addr⟩
          rw [hm]
          cases eff
          simp_all
        · contradiction
  | _ => simp [writtenAt] at write

end Ptx.Scalar.Parallel.Replay

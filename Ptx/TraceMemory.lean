import Ptx.OrderedMemory
import Std

/-! Structural projection of dynamic traces. This module does not assert that an
arbitrary projection is an instruction interpreter or that Graph.Valid suffices
for general dependent PTX. Concrete adapters discharge those separate obligations. -/
namespace Ptx.TraceMemory

inductive StorageKey where
  | global (allocation : Nat)
  | shared (device grid cluster cta allocation : Nat)
  deriving DecidableEq, Repr

/-- A catalogue slot and word offset; catalogue entries identify live storage. -/
structure Location (k : Nat) where
  storage : Fin k
  word : Nat
  deriving DecidableEq, Repr

def Location.code (a : Location k) : Nat := k * a.word + a.storage.val

theorem Location.code_injective : Function.Injective (@Location.code k) := by
  intro a b h
  have hk : 0 < k := Nat.lt_of_le_of_lt (Nat.zero_le a.storage.val) a.storage.isLt
  have hs := congrArg (· % k) h
  have hw := congrArg (· / k) h
  simp only [Location.code, Nat.mul_add_mod, Nat.mod_eq_of_lt a.storage.isLt,
    Nat.mod_eq_of_lt b.storage.isLt] at hs
  simp only [Location.code, Nat.mul_add_div hk, Nat.div_eq_of_lt a.storage.isLt,
    Nat.div_eq_of_lt b.storage.isLt, Nat.add_zero] at hw
  have hs' := Fin.ext hs
  cases a; cases b
  simp_all

theorem Location.code_eq_iff (a b : Location k) : a.code = b.code ↔ a = b :=
  ⟨fun h => Location.code_injective h, congrArg Location.code⟩

/-- Storage separation is checked on the catalogue, rather than inferred from
numeric pointer equality. No ownership or lifetime proof is implicit here. -/
structure Catalogue (k : Nat) where
  key : Fin k → StorageKey
  distinct : Function.Injective key

theorem Catalogue.same_storage (c : Catalogue k) (a b : Location k)
    (h : a.code = b.code) : c.key a.storage = c.key b.storage := by
  rw [Location.code_injective h]

theorem Catalogue.different_storage (c : Catalogue k) (a b : Location k)
    (h : c.key a.storage ≠ c.key b.storage) : a.code ≠ b.code :=
  fun eq => h (c.same_storage a b eq)

inductive AccessKind where
  | load (order : LoadOrder)
  | store (order : StoreOrder)
  deriving DecidableEq, Repr

def AccessKind.op : AccessKind → EventOp
  | .load order => .load order
  | .store order => .store order

structure Access (k : Nat) where
  location : Location k
  kind : AccessKind
  value : Word
  deriving DecidableEq, Repr

def Access.effect (a : Access k) : Effect := ⟨a.kind.op, a.location.code, a.value⟩

structure Projected (k : Nat) (α : Type) where
  position : Nat
  origin : α
  access : Access k
  deriving Repr

def label (memory : α → Option (Access k)) (position : Nat) (origin : α) :
    Option (Projected k α) := (memory origin).map (fun a => ⟨position, origin, a⟩)

/-- Number before filtering: non-memory occurrences still consume positions. -/
def project (memory : α → Option (Access k)) (trace : List α) : List (Projected k α) :=
  (trace.mapIdx (label memory)).filterMap id

theorem label_eq_some_iff (memory : α → Option (Access k)) (i : Nat) (e : α)
    (p : Projected k α) : label memory i e = some p ↔
    p.position = i ∧ p.origin = e ∧ memory e = some p.access := by
  cases p
  simp only [label]
  cases h : memory e <;> simp_all [eq_comm]

theorem project_member_iff (memory : α → Option (Access k)) (trace : List α)
    (p : Projected k α) : p ∈ project memory trace ↔
    trace[p.position]? = some p.origin ∧ memory p.origin = some p.access := by
  simp only [project, List.mem_filterMap, List.mem_mapIdx]
  constructor
  · rintro ⟨_, ⟨i, hi, rfl⟩, hp⟩
    obtain ⟨pos, origin, mem⟩ := (label_eq_some_iff memory i trace[i] p).mp hp
    subst pos
    exact ⟨List.getElem?_eq_some_iff.mpr ⟨hi, origin.symm⟩, origin ▸ mem⟩
  · rintro ⟨ht, hm⟩
    obtain ⟨hi, he⟩ := List.getElem?_eq_some_iff.mp ht
    refine ⟨some p, ⟨p.position, hi, ?_⟩, rfl⟩
    exact (label_eq_some_iff _ _ _ _).mpr ⟨rfl, he.symm, he ▸ hm⟩

theorem project_complete (memory : α → Option (Access k)) (trace : List α)
    {i : Nat} {e : α} {a : Access k} (atIndex : trace[i]? = some e)
    (effect : memory e = some a) : (⟨i, e, a⟩ : Projected k α) ∈ project memory trace :=
  (project_member_iff _ _ _).mpr ⟨atIndex, effect⟩

theorem project_unique (memory : α → Option (Access k)) (trace : List α)
    {p q : Projected k α} (hp : p ∈ project memory trace) (hq : q ∈ project memory trace)
    (same : p.position = q.position) : p = q := by
  obtain ⟨ep, ap⟩ := (project_member_iff _ _ _).mp hp
  obtain ⟨eq, aq⟩ := (project_member_iff _ _ _).mp hq
  have origin : p.origin = q.origin := Option.some.inj (ep.symm.trans (same ▸ eq))
  have access : p.access = q.access := Option.some.inj (ap.symm.trans (origin ▸ aq))
  cases p; cases q; simp_all

/-- Projection retains strict dynamic order, hence cannot duplicate an occurrence. -/
theorem project_ordered (memory : α → Option (Access k)) (trace : List α) :
    (project memory trace).Pairwise (fun p q => p.position < q.position) := by
  apply List.pairwise_filterMap.mpr
  apply List.pairwise_iff_getElem.mpr
  intro i j hi hj hij p hp q hq
  simp only [List.getElem_mapIdx, id_eq] at hp hq
  have pi := (label_eq_some_iff _ _ _ _).mp hp
  have qj := (label_eq_some_iff _ _ _ _).mp hq
  omega

theorem project_nodup (memory : α → Option (Access k)) (trace : List α) :
    (project memory trace).Nodup := by
  apply List.nodup_iff_pairwise_ne.mpr
  exact (project_ordered memory trace).imp (fun h eq => by subst eq; exact Nat.lt_irrefl _ h)

def Projected.occurrence (thread : Nat) (p : Projected k α) : Occurrence :=
  ⟨some thread, p.position, p.access.effect⟩

@[simp] theorem Projected.position_preserved (thread : Nat) (p : Projected k α) :
    (p.occurrence thread).position = p.position := rfl

@[simp] theorem Projected.value_preserved (thread : Nat) (p : Projected k α) :
    (p.occurrence thread).effect.value = p.access.value := rfl

@[simp] theorem Projected.address_preserved (thread : Nat) (p : Projected k α) :
    (p.occurrence thread).effect.address = p.access.location.code := rfl

@[simp] theorem Projected.kind_preserved (thread : Nat) (p : Projected k α) :
    (p.occurrence thread).effect.op = p.access.kind.op := rfl

structure Initial (k : Nat) where
  location : Location k
  value : Word
  deriving Repr

def Initial.occurrence (i : Initial k) : Occurrence :=
  ⟨none, i.location.code, ⟨.init, i.location.code, i.value⟩⟩

/-- One combined list, so program order crosses global/shared boundaries. -/
def events (initial : List (Initial k)) (threads : List Nat)
    (trace : Nat → List α) (memory : Nat → α → Option (Access k)) : List Occurrence :=
  initial.map Initial.occurrence ++ threads.flatMap
    (fun t => (project (memory t) (trace t)).map (Projected.occurrence t))

def graph (labels : List Occurrence) (source : Fin labels.length → Fin labels.length)
    (co : Fin labels.length → Fin labels.length → Bool) : Graph labels.length :=
  ⟨fun i => labels[i], source, co⟩

@[simp] theorem graph_label (labels : List Occurrence)
    (source : Fin labels.length → Fin labels.length)
    (co : Fin labels.length → Fin labels.length → Bool) (i : Fin labels.length) :
    (graph labels source co).event i = labels[i] := rfl

/-- Dynamic program order depends on occurrence identity, not memory space or PC. -/
theorem po_iff (g : Graph n) (a b : Fin n) (p : Projected k α) (q : Projected k α)
    (t u : Nat) (ha : g.event a = p.occurrence t) (hb : g.event b = q.occurrence u) :
    g.po a b ↔ t = u ∧ p.position < q.position := by
  simp [Graph.po, ha, hb, Projected.occurrence]

theorem same_address_iff (g : Graph n) (a b : Fin n)
    (p : Projected k α) (q : Projected k α) (t u : Nat)
    (ha : g.event a = p.occurrence t) (hb : g.event b = q.occurrence u) :
    g.sameAddress a b ↔ p.access.location = q.access.location := by
  simp only [Graph.sameAddress, ha, hb, Projected.occurrence, Access.effect]
  exact Location.code_eq_iff _ _

theorem events_member_iff (initial : List (Initial k)) (threads : List Nat)
    (trace : Nat → List α) (memory : Nat → α → Option (Access k)) (e : Occurrence) :
    e ∈ events initial threads trace memory ↔
    (∃ i ∈ initial, i.occurrence = e) ∨
    (∃ t ∈ threads, ∃ p : Projected k α, (trace t)[p.position]? = some p.origin ∧
      memory t p.origin = some p.access ∧ p.occurrence t = e) := by
  simp only [events, List.mem_append, List.mem_map, List.mem_flatMap, project_member_iff]
  constructor
  · rintro (hi | ⟨t, ht, p, ⟨hp, hm⟩, he⟩)
    · exact Or.inl hi
    · exact Or.inr ⟨t, ht, p, hp, hm, he⟩
  · rintro (hi | ⟨t, ht, p, hp, hm, he⟩)
    · exact Or.inl hi
    · exact Or.inr ⟨t, ht, p, ⟨hp, hm⟩, he⟩

/-- Initial identities use location codes; program identities use thread and
all-instruction occurrence position. They occupy disjoint identity domains. -/
def identity (e : Occurrence) : Option Nat × Nat := (e.thread, e.position)

theorem events_unique (initial : List (Initial k)) (threads : List Nat)
    (trace : Nat → List α) (memory : Nat → α → Option (Access k))
    (initialUnique : (initial.map Initial.location).Nodup) (threadUnique : threads.Nodup) :
    ((events initial threads trace memory).map identity).Nodup := by
  apply List.nodup_iff_pairwise_ne.mpr
  rw [List.pairwise_map, events, List.pairwise_append]
  refine ⟨?_, ?_, ?_⟩
  · rw [List.pairwise_map]
    have hi := List.pairwise_map.mp (List.nodup_iff_pairwise_ne.mp initialUnique)
    apply hi.imp
    intro a b different same
    apply different
    exact Location.code_injective (congrArg Prod.snd same)
  · apply List.pairwise_flatMap.mpr
    constructor
    · intro t _
      rw [List.pairwise_map]
      apply (project_ordered (memory t) (trace t)).imp
      intro p q lt same
      have positions : p.position = q.position := congrArg Prod.snd same
      omega
    · apply (List.nodup_iff_pairwise_ne.mp threadUnique).imp
      intro t u different x hx y hy same
      obtain ⟨p, _, rfl⟩ := List.mem_map.mp hx
      obtain ⟨q, _, rfl⟩ := List.mem_map.mp hy
      exact different (Option.some.inj (congrArg Prod.fst same))
  · intro x hx y hy same
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hx
    obtain ⟨t, _, hp⟩ := List.mem_flatMap.mp hy
    obtain ⟨p, _, rfl⟩ := List.mem_map.mp hp
    have impossible := congrArg Prod.fst same
    simp [identity, Initial.occurrence, Projected.occurrence] at impossible

end Ptx.TraceMemory

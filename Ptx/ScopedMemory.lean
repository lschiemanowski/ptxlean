import Ptx.Environment
import Ptx.Checker

/-! Scope-aware constraints for the existing constant-store, whole-word,
generic-proxy language. This does not assert sufficiency for dependent programs.
Initialization is the same normalized initial-write convention as `Graph`.
Out-of-scope races retain whole-word sources as a NON-TORN candidate restriction;
PTX does not generally guarantee that restriction for pairs that are not morally
strong. Thus this extension does not claim complete byte-level raced outcomes. -/
namespace Ptx

structure ScopedGraph (n : Nat) where
  graph : Graph n
  topology : Nat → ThreadLocation
  scope : Fin n → Scope

namespace ScopedGraph

set_option synthInstance.maxSize 8192

def mutualScope (g : ScopedGraph n) (a b : Fin n) : Bool :=
  match (g.graph.event a).thread, (g.graph.event b).thread with
  | some ta, some tb =>
      (g.scope a).includes (g.topology ta) (g.topology tb) &&
        (g.scope b).includes (g.topology tb) (g.topology ta)
  | _, _ => false

/-- §8.7: local program order is an independent sufficient condition.
All represented accesses are strong; overlap is complete and proxy is generic. -/
def morallyStrong (g : ScopedGraph n) (a b : Fin n) : Prop :=
  ¬g.graph.initial a ∧ ¬g.graph.initial b ∧ g.graph.sameAddress a b ∧
    (g.graph.po a b ∨ g.graph.po b a ∨ g.mutualScope a b = true)

def observation (g : ScopedGraph n) (a b : Fin n) : Prop :=
  g.graph.rf a b ∧ g.morallyStrong a b

def sync (g : ScopedGraph n) (a b : Fin n) : Prop :=
  (g.graph.event a).thread ≠ (g.graph.event b).thread ∧
    ∃ w r, g.graph.releasePattern a w ∧ g.graph.acquirePattern r b ∧
      g.observation w r ∧ g.morallyStrong a b

def baseEdge (g : ScopedGraph n) (a b : Fin n) : Prop := g.graph.po a b ∨ g.sync a b
def base (g : ScopedGraph n) : Fin n → Fin n → Prop := Path g.baseEdge
def proxyBase (g : ScopedGraph n) (a b : Fin n) : Prop := g.base a b ∧ g.graph.sameAddress a b
def cause (g : ScopedGraph n) (a b : Fin n) : Prop :=
  g.proxyBase a b ∨ ∃ z, g.observation a z ∧ g.proxyBase z b
def locationEdge (g : ScopedGraph n) (a b : Fin n) : Prop :=
  (g.graph.po a b ∧ g.graph.sameAddress a b) ∨
    (g.graph.communication a b ∧ g.morallyStrong a b)

/-- §8.9.6: coherence is partial. Racy non-initial writes are not related.
The totality obligation is limited to morally strong overlapping writes;
causally related writes are handled by `Valid.coherence_cause`. -/
structure Coherent (g : ScopedGraph n) : Prop where
  typed : ∀ a b, g.graph.coherence a b →
    g.graph.write a ∧ g.graph.write b ∧ g.graph.sameAddress a b
  irrefl : ∀ a, ¬g.graph.coherence a a
  trans : ∀ a b c, g.graph.coherence a b → g.graph.coherence b c → g.graph.coherence a c
  total : ∀ a b, g.graph.write a → g.graph.write b → g.morallyStrong a b → a ≠ b →
    g.graph.coherence a b ∨ g.graph.coherence b a
  initFirst : ∀ a b, g.graph.initial a → g.graph.write b → g.graph.sameAddress a b → a ≠ b →
    g.graph.coherence a b
  justified : ∀ a b, g.graph.coherence a b →
    g.graph.initial a ∨ g.graph.initial b ∨ g.morallyStrong a b ∨ g.cause a b ∨ g.cause b a

structure Valid (g : ScopedGraph n) : Prop where
  sources : g.graph.Sources
  co : g.Coherent
  base_irrefl : ∀ a, ¬g.base a a
  coherence_cause : ∀ a b, g.graph.write a → g.graph.write b → g.graph.sameAddress a b →
    g.cause a b → g.graph.coherence a b
  no_future : ∀ r w, g.graph.read r → g.graph.write w → g.graph.sameAddress r w →
    g.cause r w → g.graph.source r ≠ w
  no_stale : ∀ w r, g.graph.write w → g.graph.read r → g.graph.sameAddress w r →
    g.cause w r → ¬g.graph.coherence (g.graph.source r) w
  sc_per_location : ∀ a, ¬Path g.locationEdge a a

instance (g : ScopedGraph n) (a b : Fin n) : Decidable (g.morallyStrong a b) := by
  unfold morallyStrong; infer_instance
instance (g : ScopedGraph n) (a b : Fin n) : Decidable (g.observation a b) := by
  unfold observation; infer_instance
instance (g : ScopedGraph n) (a b : Fin n) : Decidable (g.sync a b) := by
  unfold sync; infer_instance
instance (g : ScopedGraph n) (a b : Fin n) : Decidable (g.baseEdge a b) := by
  unfold baseEdge; infer_instance
instance (g : ScopedGraph n) (a b : Fin n) : Decidable (g.base a b) :=
  decidable_of_iff (reachable (fun x y => decide (g.baseEdge x y)) a b = true)
    (by simpa [base] using reachable_iff (fun x y => decide (g.baseEdge x y)) a b)
instance (g : ScopedGraph n) (a b : Fin n) : Decidable (g.proxyBase a b) := by
  unfold proxyBase; infer_instance
instance (g : ScopedGraph n) (a b : Fin n) : Decidable (g.cause a b) := by
  unfold cause; infer_instance
instance (g : ScopedGraph n) (a b : Fin n) : Decidable (g.locationEdge a b) := by
  unfold locationEdge; infer_instance
instance (g : ScopedGraph n) (a b : Fin n) : Decidable (Path g.locationEdge a b) :=
  decidable_of_iff (reachable (fun x y => decide (g.locationEdge x y)) a b = true)
    (by simpa using reachable_iff (fun x y => decide (g.locationEdge x y)) a b)

instance (g : ScopedGraph n) : Decidable g.Coherent :=
  decidable_of_iff
    ((∀ a b, g.graph.coherence a b → g.graph.write a ∧ g.graph.write b ∧ g.graph.sameAddress a b) ∧
     (∀ a, ¬g.graph.coherence a a) ∧
     (∀ a b c, g.graph.coherence a b → g.graph.coherence b c → g.graph.coherence a c) ∧
     (∀ a b, g.graph.write a → g.graph.write b → g.morallyStrong a b → a ≠ b →
       g.graph.coherence a b ∨ g.graph.coherence b a) ∧
     (∀ a b, g.graph.initial a → g.graph.write b → g.graph.sameAddress a b → a ≠ b →
       g.graph.coherence a b) ∧
     (∀ a b, g.graph.coherence a b →
       g.graph.initial a ∨ g.graph.initial b ∨ g.morallyStrong a b ∨ g.cause a b ∨ g.cause b a))
    ⟨fun ⟨a,b,c,d,e,f⟩ => ⟨a,b,c,d,e,f⟩,
      fun h => ⟨h.typed,h.irrefl,h.trans,h.total,h.initFirst,h.justified⟩⟩

instance (g : ScopedGraph n) : Decidable g.Valid :=
  decidable_of_iff
    (g.graph.Sources ∧ g.Coherent ∧ (∀ a, ¬g.base a a) ∧
     (∀ a b, g.graph.write a → g.graph.write b → g.graph.sameAddress a b →
       g.cause a b → g.graph.coherence a b) ∧
     (∀ r w, g.graph.read r → g.graph.write w → g.graph.sameAddress r w →
       g.cause r w → g.graph.source r ≠ w) ∧
     (∀ w r, g.graph.write w → g.graph.read r → g.graph.sameAddress w r →
       g.cause w r → ¬g.graph.coherence (g.graph.source r) w) ∧
     (∀ a, ¬Path g.locationEdge a a))
    ⟨fun ⟨a,b,c,d,e,f,h⟩ => ⟨a,b,c,d,e,f,h⟩,
      fun h => ⟨h.sources,h.co,h.base_irrefl,h.coherence_cause,h.no_future,h.no_stale,h.sc_per_location⟩⟩

/-- Every represented non-initial pair includes each other. It is satisfied by
the original one-device GPU-scoped program graphs. -/
def AllInScope (g : ScopedGraph n) : Prop :=
  ∀ a b, ¬g.graph.initial a → ¬g.graph.initial b → g.mutualScope a b = true

variable {g : ScopedGraph n}

theorem morallyStrong_legacy (h : g.AllInScope) :
    g.morallyStrong a b ↔ g.graph.morallyStrong a b := by
  constructor
  · rintro ⟨ha,hb,hab,_⟩; exact ⟨ha,hb,hab⟩
  · rintro ⟨ha,hb,hab⟩; exact ⟨ha,hb,hab,Or.inr (Or.inr (h _ _ ha hb))⟩

theorem observation_legacy (h : g.AllInScope) :
    g.observation a b ↔ g.graph.observation a b := by
  simp [observation, Graph.observation, morallyStrong_legacy h]

theorem sync_legacy (h : g.AllInScope) : g.sync a b ↔ g.graph.sync a b := by
  simp [sync, Graph.sync, observation_legacy h, morallyStrong_legacy h]

theorem base_legacy (h : g.AllInScope) : g.base a b ↔ g.graph.base a b := by
  have edges : g.baseEdge = g.graph.baseEdge := by
    funext x y
    exact propext (by simp [baseEdge, Graph.baseEdge, sync_legacy h])
  simp only [base, Graph.base, edges]

theorem cause_legacy (h : g.AllInScope) : g.cause a b ↔ g.graph.cause a b := by
  simp [cause, Graph.cause, proxyBase, Graph.proxyBase, base_legacy h, observation_legacy h]

theorem location_legacy (h : g.AllInScope) :
    Path g.locationEdge a b ↔ Path g.graph.locationEdge a b := by
  have edges : g.locationEdge = g.graph.locationEdge := by
    funext x y
    exact propext (by simp [locationEdge, Graph.locationEdge, morallyStrong_legacy h])
  rw [edges]

theorem coherent_legacy (h : g.AllInScope) : g.Coherent ↔ g.graph.Coherent := by
  constructor
  · intro hc
    refine ⟨hc.typed,hc.irrefl,hc.trans,?_,hc.initFirst⟩
    intro a b ha hb hab ne
    by_cases hia : g.graph.initial a
    · exact Or.inl (hc.initFirst a b hia hb hab ne)
    by_cases hib : g.graph.initial b
    · exact Or.inr (hc.initFirst b a hib ha hab.symm ne.symm)
    exact hc.total a b ha hb ((morallyStrong_legacy h).mpr ⟨hia,hib,hab⟩) ne
  · intro hc
    refine ⟨hc.typed,hc.irrefl,hc.trans,?_,hc.initFirst,?_⟩
    · intro a b ha hb hm ne
      exact hc.total a b ha hb hm.2.2.1 ne
    · intro a b hab
      by_cases hia : g.graph.initial a
      · exact Or.inl hia
      by_cases hib : g.graph.initial b
      · exact Or.inr (Or.inl hib)
      exact Or.inr (Or.inr (Or.inl ((morallyStrong_legacy h).mpr
        ⟨hia,hib,(hc.typed a b hab).2.2⟩)))

/-- Exact specialization; no old semantic definition is edited or weakened. -/
theorem valid_legacy (h : g.AllInScope) : g.Valid ↔ g.graph.Valid := by
  constructor
  · intro hv
    exact {
      sources := hv.sources
      co := (coherent_legacy h).mp hv.co
      base_irrefl := fun a ha => hv.base_irrefl a ((base_legacy h).mpr ha)
      coherence_cause := fun a b ha hb hab hc => hv.coherence_cause a b ha hb hab ((cause_legacy h).mpr hc)
      no_future := fun a b ha hb hab hc => hv.no_future a b ha hb hab ((cause_legacy h).mpr hc)
      no_stale := fun a b ha hb hab hc => hv.no_stale a b ha hb hab ((cause_legacy h).mpr hc)
      sc_per_location := fun a ha => hv.sc_per_location a ((location_legacy h).mpr ha)
    }
  · intro hv
    exact {
      sources := hv.sources
      co := (coherent_legacy h).mpr hv.co
      base_irrefl := fun a ha => hv.base_irrefl a ((base_legacy h).mp ha)
      coherence_cause := fun a b ha hb hab hc => hv.coherence_cause a b ha hb hab ((cause_legacy h).mp hc)
      no_future := fun a b ha hb hab hc => hv.no_future a b ha hb hab ((cause_legacy h).mp hc)
      no_stale := fun a b ha hb hab hc => hv.no_stale a b ha hb hab ((cause_legacy h).mp hc)
      sc_per_location := fun a ha => hv.sc_per_location a ((location_legacy h).mp ha)
    }

end ScopedGraph

/-- Scope labels supplement, rather than replace, the actual instruction traces. -/
def Program.scopedGraph (p : Program) (registers : Nat → Registers) (oracle : Nat → Nat → Word)
    (source : Fin (p.events registers oracle).length → Fin (p.events registers oracle).length)
    (co : Fin (p.events registers oracle).length → Fin (p.events registers oracle).length → Bool)
    (topology : Nat → ThreadLocation) (scope : Fin (p.events registers oracle).length → Scope) :
    ScopedGraph (p.events registers oracle).length :=
  ⟨p.graph registers oracle source co, topology, scope⟩

/-- Distinct threads in the program have distinct physical identities. -/
def Program.TopologyWellFormed (p : Program) (topology : Nat → ThreadLocation) : Prop :=
  ∀ i, i < p.threads.length → ∀ j, j < p.threads.length → topology i = topology j → i = j

/-- A bounded constant-store candidate with injective used-thread identities.
The arena is still global and word-addressed. `Environment.checkAccess` and target
eligibility are separate contracts, not silently implied by this predicate. -/
def Program.ScopedAdmitted (p : Program) (registers : Nat → Registers) (oracle : Nat → Nat → Word)
    (source : Fin (p.events registers oracle).length → Fin (p.events registers oracle).length)
    (co : Fin (p.events registers oracle).length → Fin (p.events registers oracle).length → Bool)
    (topology : Nat → ThreadLocation) (scope : Fin (p.events registers oracle).length → Scope) : Prop :=
  p.Bounded ∧ p.TopologyWellFormed topology ∧
    (p.scopedGraph registers oracle source co topology scope).Valid

end Ptx

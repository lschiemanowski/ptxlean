import Ptx.Language

/-!
Restricted PTX 9.4 memory relations for constant-address, aligned u32 global
loads/stores at GPU scope, generic proxy, one device. Initialization is a
separate source/coherence event with no issuing thread. See the source ledger.
-/
namespace Ptx

/-- Nonempty finite relational path. No bounded search or scheduler is assumed. -/
inductive Path (r : α → α → Prop) : α → α → Prop where
  | edge : r a b → Path r a b
  | join : Path r a b → Path r b c → Path r a c

namespace Path

variable {α : Type u} {r s : α → α → Prop} {a b : α}

theorem contained (edge : ∀ a b, r a b → s a b)
    (trans : ∀ a b c, s a b → s b c → s a c)
    (h : Path r a b) : s a b := by
  induction h with
  | edge h => exact edge _ _ h
  | join _ _ ih₁ ih₂ => exact trans _ _ _ ih₁ ih₂

theorem rank_increases (rank : α → Nat)
    (increases : ∀ a b, r a b → rank a < rank b)
    (h : Path r a b) : rank a < rank b := by
  exact contained (s := fun x y => rank x < rank y) increases
    (fun _ _ _ hab hbc => Nat.lt_trans hab hbc) h

end Path

structure Occurrence where
  thread : Option Nat
  position : Nat
  effect : Effect
  deriving DecidableEq, Repr

/-- Fixed event labels; the completed local traces supply these labels. -/
structure Graph (n : Nat) where
  event : Fin n → Occurrence
  source : Fin n → Fin n
  co : Fin n → Fin n → Bool

namespace Graph

def read (g : Graph n) (e : Fin n) : Prop :=
  match (g.event e).effect.op with | .load _ => True | _ => False

def write (g : Graph n) (e : Fin n) : Prop :=
  match (g.event e).effect.op with | .store _ | .init => True | _ => False

instance (g : Graph n) (e : Fin n) : Decidable (g.read e) := by
  unfold read
  split <;> infer_instance

instance (g : Graph n) (e : Fin n) : Decidable (g.write e) := by
  unfold write
  split <;> infer_instance

def initial (g : Graph n) (e : Fin n) : Prop := (g.event e).effect.op = .init

def acquire (g : Graph n) (e : Fin n) : Prop :=
  (g.event e).effect.op = .load .acquire

def release (g : Graph n) (e : Fin n) : Prop :=
  (g.event e).effect.op = .store .release

def sameAddress (g : Graph n) (a b : Fin n) : Prop :=
  (g.event a).effect.address = (g.event b).effect.address

/-- §8.9.1: only events of a single program thread, ordered by occurrence. -/
def po (g : Graph n) (a b : Fin n) : Prop :=
  (g.event a).thread ≠ none ∧ (g.event a).thread = (g.event b).thread ∧
  (g.event a).position < (g.event b).position

/-- §8.7 restricted to strong GPU/generic program accesses with full overlap. -/
def morallyStrong (g : Graph n) (a b : Fin n) : Prop :=
  ¬g.initial a ∧ ¬g.initial b ∧ g.sameAddress a b

/-- Read-source choices, not a synchronizes-with relation. -/
def rf (g : Graph n) (a b : Fin n) : Prop := g.read b ∧ g.source b = a

def coherence (g : Graph n) (a b : Fin n) : Prop := g.co a b = true

/-- §8.9.2, with no RMW operations in the language. -/
def observation (g : Graph n) (a b : Fin n) : Prop :=
  g.rf a b ∧ g.morallyStrong a b

/-- §8.8: direct release or release followed by a strong write at that address. -/
def releasePattern (g : Graph n) (a w : Fin n) : Prop :=
  (a = w ∧ g.release a) ∨
  (g.release a ∧ g.write w ∧ ¬g.initial w ∧ g.po a w ∧ g.sameAddress a w)

/-- §8.8: direct acquire or strong read followed by acquire at that address. -/
def acquirePattern (g : Graph n) (r b : Fin n) : Prop :=
  (r = b ∧ g.acquire b) ∨
  (g.read r ∧ g.acquire b ∧ g.po r b ∧ g.sameAddress r b)

/-- §8.9.4: pattern endpoints must also be morally strong. -/
def sync (g : Graph n) (a b : Fin n) : Prop :=
  (g.event a).thread ≠ (g.event b).thread ∧
    ∃ w r, g.releasePattern a w ∧ g.acquirePattern r b ∧
      g.observation w r ∧ g.morallyStrong a b

def baseEdge (g : Graph n) (a b : Fin n) : Prop := g.po a b ∨ g.sync a b

def base (g : Graph n) : Fin n → Fin n → Prop := Path g.baseEdge

/-- §8.9.5, identity addressing and generic proxy: preserve same-address base. -/
def proxyBase (g : Graph n) (a b : Fin n) : Prop := g.base a b ∧ g.sameAddress a b

/-- Do NOT transitively close this relation: §8.9.5's second clause matters. -/
def cause (g : Graph n) (a b : Fin n) : Prop :=
  g.proxyBase a b ∨ ∃ z, g.observation a z ∧ g.proxyBase z b

/-- §8.9.7: RF, coherence, and from-read. -/
def communication (g : Graph n) (a b : Fin n) : Prop :=
  g.rf a b ∨ g.coherence a b ∨
    (g.read a ∧ g.coherence (g.source a) b)

/-- §8.10.5: overlapping PO only; not a global SC union. -/
def locationEdge (g : Graph n) (a b : Fin n) : Prop :=
  (g.po a b ∧ g.sameAddress a b) ∨
  (g.communication a b ∧ g.morallyStrong a b)

structure Sources (g : Graph n) : Prop where
  compatible : ∀ r, g.read r → g.write (g.source r) ∧
    g.sameAddress (g.source r) r ∧
    (g.event (g.source r)).effect.value = (g.event r).effect.value

/-- All program accesses at a common word are strong and mutually in scope. -/
structure Coherent (g : Graph n) : Prop where
  typed : ∀ a b, g.coherence a b → g.write a ∧ g.write b ∧ g.sameAddress a b
  irrefl : ∀ a, ¬g.coherence a a
  trans : ∀ a b c, g.coherence a b → g.coherence b c → g.coherence a c
  total : ∀ a b, g.write a → g.write b → g.sameAddress a b → a ≠ b →
    g.coherence a b ∨ g.coherence b a
  initFirst : ∀ a b, g.initial a → g.write b → g.sameAddress a b → a ≠ b →
    g.coherence a b

/-- Memory constraints, never an assumed publication/output property.
Fence-SC and RMW axioms have no instances in this typed fragment. Whole-word
sources encode single-copy atomicity; literal stores provide value grounding.
Initialization normalization and these restrictions are explained in the ledger. -/
structure Valid (g : Graph n) : Prop where
  sources : g.Sources
  co : g.Coherent
  base_irrefl : ∀ a, ¬g.base a a
  coherence_cause : ∀ a b, g.write a → g.write b → g.sameAddress a b →
    g.cause a b → g.coherence a b
  no_future : ∀ r w, g.read r → g.write w → g.sameAddress r w →
    g.cause r w → g.source r ≠ w
  no_stale : ∀ w r, g.write w → g.read r → g.sameAddress w r →
    g.cause w r → ¬g.coherence (g.source r) w
  sc_per_location : ∀ a, ¬Path g.locationEdge a a

/-- Uniform per-byte lifting: every byte in a read uses its one word source. -/
def byteSource (g : Graph n) (r : Fin n) (_offset : Fin 4) : Fin n := g.source r

theorem single_copy (g : Graph n) (r : Fin n) (i j : Fin 4) :
    g.byteSource r i = g.byteSource r j := rfl

theorem no_source_coherence_predecessor {g : Graph n} {r w : Fin n} {i j : Fin 4} (h : g.Valid)
    (same : g.byteSource r i = w) : ¬g.coherence (g.byteSource r j) w := by
  simpa [byteSource, ← same] using h.co.irrefl (g.source r)

/-- A reusable sound certificate for a finite witness. `upper` is only a proof
upper bound on derived base paths; it is not supplied as the actual semantics. -/
def upperCause (g : Graph n) (upper : Fin n → Fin n → Prop) (a b : Fin n) : Prop :=
  (upper a b ∧ g.sameAddress a b) ∨
    ∃ z, g.observation a z ∧ upper z b ∧ g.sameAddress z b

structure Certificate (g : Graph n) (upper : Fin n → Fin n → Prop)
    (rank : Fin n → Nat) : Prop where
  sources : g.Sources
  co : g.Coherent
  edge_included : ∀ a b, g.baseEdge a b → upper a b
  upper_trans : ∀ a b c, upper a b → upper b c → upper a c
  upper_irrefl : ∀ a, ¬upper a a
  coherence_cause : ∀ a b, g.write a → g.write b → g.sameAddress a b →
    g.upperCause upper a b → g.coherence a b
  no_future : ∀ r w, g.read r → g.write w → g.sameAddress r w →
    g.upperCause upper r w → g.source r ≠ w
  no_stale : ∀ w r, g.write w → g.read r → g.sameAddress w r →
    g.upperCause upper w r → ¬g.coherence (g.source r) w
  location_rank : ∀ a b, g.locationEdge a b → rank a < rank b

theorem valid_of_certificate {g : Graph n} {upper : Fin n → Fin n → Prop}
    {rank : Fin n → Nat} (h : g.Certificate upper rank) : g.Valid := by
  have bound : ∀ a b, g.base a b → upper a b :=
    fun _ _ hp => Path.contained h.edge_included h.upper_trans hp
  have causeBound : ∀ a b, g.cause a b → g.upperCause upper a b := by
    intro a b hc
    rcases hc with ⟨hb, ha⟩ | ⟨z, ho, hb, ha⟩
    · exact Or.inl ⟨bound _ _ hb, ha⟩
    · exact Or.inr ⟨z, ho, bound _ _ hb, ha⟩
  exact {
    sources := h.sources
    co := h.co
    base_irrefl := fun a hp => h.upper_irrefl a (bound _ _ hp)
    coherence_cause := fun a b hw hw' ha hc =>
      h.coherence_cause a b hw hw' ha (causeBound _ _ hc)
    no_future := fun r w hr hw ha hc => h.no_future r w hr hw ha (causeBound _ _ hc)
    no_stale := fun w r hw hr ha hc => h.no_stale w r hw hr ha (causeBound _ _ hc)
    sc_per_location := fun a hp => Nat.lt_irrefl _ (Path.rank_increases rank h.location_rank hp)
  }

end Graph
end Ptx

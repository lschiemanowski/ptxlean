import Ptx.Program
import Ptx.Reachability

/-! An exact finite decision procedure for the existing relational semantics.
This checks one fully specified candidate, not all executions of a program. -/
namespace Ptx.Graph

set_option synthInstance.maxSize 4096

instance (g : Graph n) (a : Fin n) : Decidable (g.initial a) := by
  unfold initial; infer_instance
instance (g : Graph n) (a : Fin n) : Decidable (g.acquire a) := by
  unfold acquire; infer_instance
instance (g : Graph n) (a : Fin n) : Decidable (g.release a) := by
  unfold release; infer_instance
instance (g : Graph n) (a b : Fin n) : Decidable (g.sameAddress a b) := by
  unfold sameAddress; infer_instance
instance (g : Graph n) (a b : Fin n) : Decidable (g.po a b) := by
  unfold po; infer_instance
instance (g : Graph n) (a b : Fin n) : Decidable (g.morallyStrong a b) := by
  unfold morallyStrong; infer_instance
instance (g : Graph n) (a b : Fin n) : Decidable (g.rf a b) := by
  unfold rf; infer_instance
instance (g : Graph n) (a b : Fin n) : Decidable (g.coherence a b) := by
  unfold coherence; infer_instance
instance (g : Graph n) (a b : Fin n) : Decidable (g.observation a b) := by
  unfold observation; infer_instance
instance (g : Graph n) (a b : Fin n) : Decidable (g.releasePattern a b) := by
  unfold releasePattern; infer_instance
instance (g : Graph n) (a b : Fin n) : Decidable (g.acquirePattern a b) := by
  unfold acquirePattern; infer_instance
instance (g : Graph n) (a b : Fin n) : Decidable (g.sync a b) := by
  unfold sync; infer_instance
instance (g : Graph n) (a b : Fin n) : Decidable (g.baseEdge a b) := by
  unfold baseEdge; infer_instance
instance (g : Graph n) (a b : Fin n) : Decidable (g.communication a b) := by
  unfold communication; infer_instance
instance (g : Graph n) (a b : Fin n) : Decidable (g.locationEdge a b) := by
  unfold locationEdge; infer_instance

instance (g : Graph n) : Decidable g.Sources :=
  decidable_of_iff (∀ r, g.read r → g.write (g.source r) ∧
    g.sameAddress (g.source r) r ∧
    (g.event (g.source r)).effect.value = (g.event r).effect.value)
    ⟨Sources.mk, Sources.compatible⟩

instance (g : Graph n) : Decidable g.Coherent :=
  decidable_of_iff
    ((∀ a b, g.coherence a b → g.write a ∧ g.write b ∧ g.sameAddress a b) ∧
     (∀ a, ¬g.coherence a a) ∧
     (∀ a b c, g.coherence a b → g.coherence b c → g.coherence a c) ∧
     (∀ a b, g.write a → g.write b → g.sameAddress a b → a ≠ b →
       g.coherence a b ∨ g.coherence b a) ∧
     (∀ a b, g.initial a → g.write b → g.sameAddress a b → a ≠ b → g.coherence a b))
    ⟨fun ⟨ht, hi, hx, ho, hf⟩ => ⟨ht, hi, hx, ho, hf⟩,
     fun h => ⟨h.typed, h.irrefl, h.trans, h.total, h.initFirst⟩⟩

def baseCheck (g : Graph n) : Fin n → Fin n → Bool :=
  reachable (fun a b => decide (g.baseEdge a b))

theorem baseCheck_iff (g : Graph n) (a b : Fin n) :
    g.baseCheck a b = true ↔ g.base a b := by
  simpa [baseCheck, base] using
    reachable_iff (fun a b => decide (g.baseEdge a b)) a b

def causeCheck (g : Graph n) (a b : Fin n) : Bool :=
  decide ((g.baseCheck a b = true ∧ g.sameAddress a b) ∨
    ∃ z, g.observation a z ∧ g.baseCheck z b = true ∧ g.sameAddress z b)

theorem causeCheck_iff (g : Graph n) (a b : Fin n) :
    g.causeCheck a b = true ↔ g.cause a b := by
  simp [causeCheck, cause, proxyBase, baseCheck_iff]

def locationCheck (g : Graph n) : Fin n → Fin n → Bool :=
  reachable (fun a b => decide (g.locationEdge a b))

theorem locationCheck_iff (g : Graph n) (a b : Fin n) :
    g.locationCheck a b = true ↔ Path g.locationEdge a b := by
  simpa [locationCheck] using
    reachable_iff (fun a b => decide (g.locationEdge a b)) a b

/-- All clauses are finite; reachability is exact rather than a depth cutoff. -/
def check (g : Graph n) : Bool := decide (
    g.Sources ∧ g.Coherent ∧
    (∀ a, ¬g.baseCheck a a = true) ∧
    (∀ a b, g.write a → g.write b → g.sameAddress a b →
      g.causeCheck a b = true → g.coherence a b) ∧
    (∀ r w, g.read r → g.write w → g.sameAddress r w →
      g.causeCheck r w = true → g.source r ≠ w) ∧
    (∀ w r, g.write w → g.read r → g.sameAddress w r →
      g.causeCheck w r = true → ¬g.coherence (g.source r) w) ∧
    (∀ a, ¬g.locationCheck a a = true))

/-- Sound and complete for every finite graph, including graphs not materialized
from a program. Program admission separately requires generated labels and bounds. -/
theorem check_iff (g : Graph n) : g.check = true ↔ g.Valid := by
  simp only [check, decide_eq_true_eq, baseCheck_iff, causeCheck_iff, locationCheck_iff]
  exact ⟨fun ⟨hs, hc, hb, hw, hf, ho, hl⟩ => ⟨hs, hc, hb, hw, hf, ho, hl⟩,
    fun h => ⟨h.sources, h.co, h.base_irrefl, h.coherence_cause,
      h.no_future, h.no_stale, h.sc_per_location⟩⟩

theorem check_false_iff (g : Graph n) : g.check = false ↔ ¬g.Valid := by
  rw [← check_iff]
  cases g.check <;> simp

end Ptx.Graph

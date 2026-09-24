import Ptx.SharedReductionMemoryOrder

/-! A sufficient finite serial certificate used to construct a selected witness.
Its local obligations must be proved from an actual trace. This is not a new
PTX admissibility criterion and does not constrain universal candidates. -/
namespace Ptx.Scalar.SharedReduction.Machine.Memory

/-- A chronological proof certificate, with explicit source/latest obligations. -/
structure SerialCertificate (g : Graph m) (extra : Fin m → Fin m → Prop)
    (rank : Fin m → Nat) : Prop where
  injective : Function.Injective rank
  sources : g.Sources
  source_before : ∀ r, g.read r → rank (g.source r) < rank r
  latest : ∀ w r, g.write w → g.read r → g.sameAddress w r →
    rank w < rank r → rank w ≤ rank (g.source r)
  coherence_iff : ∀ a b, g.coherence a b ↔
    g.write a ∧ g.write b ∧ g.sameAddress a b ∧ rank a < rank b
  initial_before : ∀ i w, g.initial i → g.write w → g.sameAddress i w →
    i ≠ w → rank i < rank w
  base_before : ∀ a b, Graph.Ordered.baseEdge g extra a b → rank a < rank b

private theorem read_not_write (g : Graph m) (e : Fin m) (read : g.read e) : ¬g.write e := by
  cases op : (g.event e).effect.op <;> simp [Graph.read,Graph.write,op] at *

/-- Explicitly checked source and rank obligations imply the original constraints. -/
theorem SerialCertificate.valid {g : Graph m} {extra : Fin m → Fin m → Prop}
    {rank : Fin m → Nat} (cert : SerialCertificate g extra rank) : Graph.Ordered.Valid g extra := by
  have causeRank : ∀ a b, g.upperCause (fun a b => rank a < rank b) a b → rank a < rank b := by
    intro a b cause
    rcases cause with ⟨h,_⟩ | ⟨z,obs,h,_⟩
    · exact h
    · have rf := obs.1
      have earlier := cert.source_before z rf.1
      rw [rf.2] at earlier
      omega
  have coherent : g.Coherent := {
    typed := by
      intro a b co
      have h := (cert.coherence_iff a b).mp co
      exact ⟨h.1,h.2.1,h.2.2.1⟩
    irrefl := by
      intro a co
      have h := (cert.coherence_iff a a).mp co
      exact Nat.lt_irrefl _ h.2.2.2
    trans := by
      intro a b c ab bc
      have ha := (cert.coherence_iff a b).mp ab
      have hb := (cert.coherence_iff b c).mp bc
      exact (cert.coherence_iff a c).mpr
        ⟨ha.1,hb.2.1,ha.2.2.1.trans hb.2.2.1,Nat.lt_trans ha.2.2.2 hb.2.2.2⟩
    total := by
      intro a b wa wb same different
      have ne : rank a ≠ rank b := fun h => different (cert.injective h)
      rcases Nat.lt_or_gt_of_ne ne with lt | gt
      · exact .inl ((cert.coherence_iff a b).mpr ⟨wa,wb,same,lt⟩)
      · exact .inr ((cert.coherence_iff b a).mpr ⟨wb,wa,same.symm,gt⟩)
    initFirst := by
      intro i w initial write same different
      have wi : g.write i := by
        change (g.event i).effect.op = .init at initial
        simp [Graph.write,initial]
      exact (cert.coherence_iff i w).mpr
        ⟨wi,write,same,cert.initial_before i w initial write same different⟩
  }
  apply Graph.Ordered.valid_of_certificate (upper := fun a b => rank a < rank b) (rank := rank)
  exact {
    sources := cert.sources
    co := coherent
    edge_included := cert.base_before
    upper_trans := fun _ _ _ => Nat.lt_trans
    upper_irrefl := fun _ => Nat.lt_irrefl _
    coherence_cause := fun a b wa wb same cause =>
      (cert.coherence_iff a b).mpr ⟨wa,wb,same,causeRank a b cause⟩
    no_future := by
      intro r w read write same cause equal
      have future := causeRank r w cause
      have past := cert.source_before r read
      rw [equal] at past
      omega
    no_stale := by
      intro w r write read same cause co
      have bound := cert.latest w r write read same (causeRank w r cause)
      have earlier := ((cert.coherence_iff _ _).mp co).2.2.2
      omega
    location_rank := by
      intro a b edge
      rcases edge with ⟨po,_⟩ | ⟨communication,_⟩
      · exact cert.base_before a b (.inl (.inl po))
      · rcases communication with rf | co | ⟨read,co⟩
        · have earlier := cert.source_before b rf.1
          rw [rf.2] at earlier
          exact earlier
        · exact ((cert.coherence_iff a b).mp co).2.2.2
        · have coFacts := (cert.coherence_iff (g.source a) b).mp co
          have sourceAddress := (cert.sources.compatible a read).2.1
          have same : g.sameAddress b a := coFacts.2.2.1.symm.trans sourceAddress
          have ne : rank a ≠ rank b := by
            intro equal
            have sameEvent := cert.injective equal
            exact read_not_write g a read (sameEvent ▸ coFacts.2.1)
          rcases Nat.lt_or_gt_of_ne ne with lt | gt
          · exact lt
          · have bound := cert.latest b a coFacts.2.1 read same gt
            omega
  }

/-- The same certificate separately excludes cycles through all actual base
edges and read-source edges. This is a conservative grounding relation. -/
def grounding (g : Graph m) (extra : Fin m → Fin m → Prop) (a b : Fin m) : Prop :=
  Graph.Ordered.baseEdge g extra a b ∨ g.rf a b

theorem SerialCertificate.grounded {g : Graph m} {extra : Fin m → Fin m → Prop}
    {rank : Fin m → Nat} (cert : SerialCertificate g extra rank) (a : Fin m) :
    ¬Path (grounding g extra) a a := by
  intro cycle
  apply Nat.lt_irrefl (rank a)
  apply Path.rank_increases rank _ cycle
  intro x y edge
  rcases edge with base | rf
  · exact cert.base_before x y base
  · have h := cert.source_before y rf.1
    simpa [rf.2] using h

end Ptx.Scalar.SharedReduction.Machine.Memory

import Ptx.Publication

/-!
A conservative extension of whole-word memory constraints by additional base
order. `extra` is a parameter whose execution and source justification belong
to an application; accepting this parameter is not a barrier implementation.
In particular, this file does not silently change global accesses to shared ones.
-/
namespace Ptx.Graph.Ordered

variable {n : Nat}

def baseEdge (g : Graph n) (extra : Fin n → Fin n → Prop) (a b : Fin n) : Prop :=
  g.baseEdge a b ∨ extra a b

def base (g : Graph n) (extra : Fin n → Fin n → Prop) : Fin n → Fin n → Prop :=
  Path (baseEdge g extra)

def cause (g : Graph n) (extra : Fin n → Fin n → Prop) (a b : Fin n) : Prop :=
  (base g extra a b ∧ g.sameAddress a b) ∨
    ∃ z, g.observation a z ∧ base g extra z b ∧ g.sameAddress z b

/-- The same memory axioms, with the additional justified base order. No result
value, termination claim or execution-origin assertion is a field of this type. -/
structure Valid (g : Graph n) (extra : Fin n → Fin n → Prop) : Prop where
  sources : g.Sources
  co : g.Coherent
  base_irrefl : ∀ a, ¬base g extra a a
  coherence_cause : ∀ a b, g.write a → g.write b → g.sameAddress a b →
    cause g extra a b → g.coherence a b
  no_future : ∀ r w, g.read r → g.write w → g.sameAddress r w →
    cause g extra r w → g.source r ≠ w
  no_stale : ∀ w r, g.write w → g.read r → g.sameAddress w r →
    cause g extra w r → ¬g.coherence (g.source r) w
  sc_per_location : ∀ a, ¬Path g.locationEdge a a

theorem base_mono (g : Graph n) {small large : Fin n → Fin n → Prop}
    (included : ∀ a b, small a b → large a b) {a b : Fin n}
    (h : base g small a b) : base g large a b := by
  exact Path.contained
    (fun _ _ edge => Path.edge (edge.elim Or.inl (fun h => Or.inr (included _ _ h))))
    (fun _ _ _ => Path.join) h

theorem cause_mono (g : Graph n) {small large : Fin n → Fin n → Prop}
    (included : ∀ a b, small a b → large a b) {a b : Fin n}
    (h : cause g small a b) : cause g large a b := by
  rcases h with ⟨hb, hs⟩ | ⟨z, ho, hb, hs⟩
  · exact Or.inl ⟨base_mono g included hb, hs⟩
  · exact Or.inr ⟨z, ho, base_mono g included hb, hs⟩

/-- Additional ordering makes validity harder, never easier. -/
theorem valid_restrict (g : Graph n) {small large : Fin n → Fin n → Prop}
    (included : ∀ a b, small a b → large a b) (h : Valid g large) : Valid g small := by
  exact {
    sources := h.sources
    co := h.co
    base_irrefl := fun a ha => h.base_irrefl a (base_mono g included ha)
    coherence_cause := fun a b hw hw' hs hc =>
      h.coherence_cause a b hw hw' hs (cause_mono g included hc)
    no_future := fun r w hr hw hs hc =>
      h.no_future r w hr hw hs (cause_mono g included hc)
    no_stale := fun w r hw hr hs hc =>
      h.no_stale w r hw hr hs (cause_mono g included hc)
    sc_per_location := h.sc_per_location
  }

theorem original_base (g : Graph n) (extra : Fin n → Fin n → Prop)
    {a b : Fin n} (h : g.base a b) : base g extra a b := by
  exact Path.contained (fun _ _ edge => Path.edge (Or.inl edge))
    (fun _ _ _ => Path.join) h

theorem original_cause (g : Graph n) (extra : Fin n → Fin n → Prop)
    {a b : Fin n} (h : g.cause a b) : cause g extra a b := by
  rcases h with ⟨hb, hs⟩ | ⟨z, ho, hb, hs⟩
  · exact Or.inl ⟨original_base g extra hb, hs⟩
  · exact Or.inr ⟨z, ho, original_base g extra hb, hs⟩

theorem valid_original (g : Graph n) (extra : Fin n → Fin n → Prop)
    (h : Valid g extra) : g.Valid := by
  exact {
    sources := h.sources
    co := h.co
    base_irrefl := fun a ha => h.base_irrefl a (original_base g extra ha)
    coherence_cause := fun a b hw hw' hs hc =>
      h.coherence_cause a b hw hw' hs (original_cause g extra hc)
    no_future := fun r w hr hw hs hc =>
      h.no_future r w hr hw hs (original_cause g extra hc)
    no_stale := fun w r hw hr hs hc =>
      h.no_stale w r hw hr hs (original_cause g extra hc)
    sc_per_location := h.sc_per_location
  }

theorem empty_base_iff (g : Graph n) (a b : Fin n) :
    base g (fun _ _ => False) a b ↔ g.base a b := by
  constructor
  · exact Path.contained (fun _ _ edge => Path.edge (edge.resolve_right id))
      (fun _ _ _ => Path.join)
  · exact original_base g _

theorem empty_cause_iff (g : Graph n) (a b : Fin n) :
    cause g (fun _ _ => False) a b ↔ g.cause a b := by
  simp only [cause, Graph.cause, Graph.proxyBase, empty_base_iff]

theorem empty_valid_iff (g : Graph n) :
    Valid g (fun _ _ => False) ↔ g.Valid := by
  constructor
  · exact valid_original g _
  · intro h
    exact {
      sources := h.sources
      co := h.co
      base_irrefl := fun a ha => h.base_irrefl a ((empty_base_iff g a a).mp ha)
      coherence_cause := fun a b hw hw' hs hc =>
        h.coherence_cause a b hw hw' hs ((empty_cause_iff g a b).mp hc)
      no_future := fun r w hr hw hs hc =>
        h.no_future r w hr hw hs ((empty_cause_iff g r w).mp hc)
      no_stale := fun w r hw hr hs hc =>
        h.no_stale w r hw hr hs ((empty_cause_iff g w r).mp hc)
      sc_per_location := h.sc_per_location
    }

/-- Edges already justified by original base paths do not change validity. -/
theorem derived_valid_iff (g : Graph n) (extra : Fin n → Fin n → Prop)
    (derived : ∀ a b, extra a b → g.base a b) : Valid g extra ↔ g.Valid := by
  have bound : ∀ a b, base g extra a b → g.base a b := by
    intro a b h
    exact Path.contained
      (fun x y edge => edge.elim Path.edge (derived x y))
      (fun _ _ _ => Path.join) h
  have causes : ∀ a b, cause g extra a b → g.cause a b := by
    intro a b h
    rcases h with ⟨hb, hs⟩ | ⟨z, ho, hb, hs⟩
    · exact Or.inl ⟨bound _ _ hb, hs⟩
    · exact Or.inr ⟨z, ho, bound _ _ hb, hs⟩
  constructor
  · exact valid_original g extra
  · intro h
    exact {
      sources := h.sources
      co := h.co
      base_irrefl := fun a ha => h.base_irrefl a (bound _ _ ha)
      coherence_cause := fun a b hw hw' hs hc =>
        h.coherence_cause a b hw hw' hs (causes _ _ hc)
      no_future := fun r w hr hw hs hc =>
        h.no_future r w hr hw hs (causes _ _ hc)
      no_stale := fun w r hw hr hs hc =>
        h.no_stale w r hw hr hs (causes _ _ hc)
      sc_per_location := h.sc_per_location
    }

theorem extra_cause (g : Graph n) (extra : Fin n → Fin n → Prop) (a b : Fin n)
    (edge : extra a b) (same : g.sameAddress a b) : cause g extra a b :=
  Or.inl ⟨Path.edge (Or.inr edge), same⟩

theorem source_of_latest (g : Graph n) (extra : Fin n → Fin n → Prop)
    (valid : Valid g extra) (w r : Fin n)
    (written : g.write w) (readAt : g.read r) (same : g.sameAddress w r)
    (ordered : cause g extra w r)
    (latest : ∀ v, g.write v → g.sameAddress v r → v ≠ w → g.coherence v w) :
    g.source r = w := by
  by_cases h : g.source r = w
  · exact h
  · have compatible := valid.sources.compatible r readAt
    exact False.elim (valid.no_stale w r written readAt same ordered
      (latest (g.source r) compatible.1 compatible.2.1 h))

/-- Values follow from source identity, after the ordering argument. -/
theorem value_of_latest (g : Graph n) (extra : Fin n → Fin n → Prop)
    (valid : Valid g extra) (w r : Fin n)
    (written : g.write w) (readAt : g.read r) (same : g.sameAddress w r)
    (ordered : cause g extra w r)
    (latest : ∀ v, g.write v → g.sameAddress v r → v ≠ w → g.coherence v w) :
    (g.event r).effect.value = (g.event w).effect.value := by
  exact Graph.value_of_source g valid.sources w r readAt
    (source_of_latest g extra valid w r written readAt same ordered latest)

/-- A witness certificate checks bounds on derived paths; `upper` does not
replace the actual order or impose an assumed output property. -/
structure Certificate (g : Graph n) (extra upper : Fin n → Fin n → Prop)
    (rank : Fin n → Nat) : Prop where
  sources : g.Sources
  co : g.Coherent
  edge_included : ∀ a b, baseEdge g extra a b → upper a b
  upper_trans : ∀ a b c, upper a b → upper b c → upper a c
  upper_irrefl : ∀ a, ¬upper a a
  coherence_cause : ∀ a b, g.write a → g.write b → g.sameAddress a b →
    g.upperCause upper a b → g.coherence a b
  no_future : ∀ r w, g.read r → g.write w → g.sameAddress r w →
    g.upperCause upper r w → g.source r ≠ w
  no_stale : ∀ w r, g.write w → g.read r → g.sameAddress w r →
    g.upperCause upper w r → ¬g.coherence (g.source r) w
  location_rank : ∀ a b, g.locationEdge a b → rank a < rank b

theorem valid_of_certificate {g : Graph n} {extra upper : Fin n → Fin n → Prop}
    {rank : Fin n → Nat} (h : Certificate g extra upper rank) : Valid g extra := by
  have bound : ∀ a b, base g extra a b → upper a b :=
    fun _ _ hp => Path.contained h.edge_included h.upper_trans hp
  have causeBound : ∀ a b, cause g extra a b → g.upperCause upper a b := by
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

end Ptx.Graph.Ordered

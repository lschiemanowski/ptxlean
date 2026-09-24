import Ptx.OrderedMemory

/-! Structural graph transport: bijective event numbering and injective address
renaming preserve and reflect the existing axioms, without adding memory rules. -/
namespace Ptx.GraphTransport

/-- `toOld` maps each new event identity to its original identity. -/
structure IndexEquiv (n m : Nat) where
  toOld : Fin m → Fin n
  toNew : Fin n → Fin m
  old_new : ∀ i, toOld (toNew i) = i
  new_old : ∀ i, toNew (toOld i) = i

def IndexEquiv.refl (n : Nat) : IndexEquiv n n := ⟨id, id, fun _ => rfl, fun _ => rfl⟩
def IndexEquiv.symm (e : IndexEquiv n m) : IndexEquiv m n :=
  ⟨e.toNew, e.toOld, e.new_old, e.old_new⟩

theorem IndexEquiv.injective (e : IndexEquiv n m) : Function.Injective e.toOld := by
  intro a b equal
  have same := congrArg e.toNew equal
  simpa only [e.new_old] using same

theorem IndexEquiv.eq_iff (e : IndexEquiv n m) (a b : Fin m) :
    e.toOld a = e.toOld b ↔ a = b := ⟨fun h => e.injective h, congrArg e.toOld⟩

theorem IndexEquiv.ne_iff (e : IndexEquiv n m) (a b : Fin m) :
    a ≠ b ↔ e.toOld a ≠ e.toOld b := (not_congr (e.eq_iff a b)).symm

theorem IndexEquiv.forall_old (e : IndexEquiv n m) (p : Fin n → Prop) :
    (∀ a, p (e.toOld a)) ↔ ∀ b, p b := by
  constructor
  · intro h b; simpa only [e.old_new] using h (e.toNew b)
  · intro h a; exact h (e.toOld a)

theorem IndexEquiv.forall_old_two (e : IndexEquiv n m) (p : Fin n → Fin n → Prop) :
    (∀ a b, p (e.toOld a) (e.toOld b)) ↔ ∀ a b, p a b := by
  constructor
  · intro h a b; simpa only [e.old_new] using h (e.toNew a) (e.toNew b)
  · intro h a b; exact h (e.toOld a) (e.toOld b)

theorem IndexEquiv.forall_old_three (e : IndexEquiv n m) (p : Fin n → Fin n → Fin n → Prop) :
    (∀ a b c, p (e.toOld a) (e.toOld b) (e.toOld c)) ↔ ∀ a b c, p a b c := by
  constructor
  · intro h a b c; simpa only [e.old_new] using h (e.toNew a) (e.toNew b) (e.toNew c)
  · intro h a b c; exact h (e.toOld a) (e.toOld b) (e.toOld c)

def occurrence (rename : Nat → Nat) (event : Occurrence) : Occurrence :=
  {event with effect := {event.effect with address := rename event.effect.address}}

def transport (g : Graph n) (e : IndexEquiv n m) (rename : Nat → Nat) : Graph m where
  event := fun i => occurrence rename (g.event (e.toOld i))
  source := fun i => e.toNew (g.source (e.toOld i))
  co := fun a b => g.co (e.toOld a) (e.toOld b)

def order (e : IndexEquiv n m) (extra : Fin n → Fin n → Prop) : Fin m → Fin m → Prop :=
  fun a b => extra (e.toOld a) (e.toOld b)

variable (g : Graph n) (e : IndexEquiv n m) (rename : Nat → Nat)
variable (injective : Function.Injective rename)

@[simp] theorem event_thread (a : Fin m) :
    ((transport g e rename).event a).thread = (g.event (e.toOld a)).thread := rfl
@[simp] theorem event_position (a : Fin m) :
    ((transport g e rename).event a).position = (g.event (e.toOld a)).position := rfl
@[simp] theorem event_op (a : Fin m) :
    ((transport g e rename).event a).effect.op = (g.event (e.toOld a)).effect.op := rfl
@[simp] theorem event_address (a : Fin m) :
    ((transport g e rename).event a).effect.address = rename (g.event (e.toOld a)).effect.address := rfl

@[simp] theorem read (a : Fin m) : (transport g e rename).read a ↔ g.read (e.toOld a) := Iff.rfl
@[simp] theorem write (a : Fin m) : (transport g e rename).write a ↔ g.write (e.toOld a) := Iff.rfl
@[simp] theorem initial (a : Fin m) : (transport g e rename).initial a ↔ g.initial (e.toOld a) := Iff.rfl
@[simp] theorem acquire (a : Fin m) : (transport g e rename).acquire a ↔ g.acquire (e.toOld a) := Iff.rfl
@[simp] theorem release (a : Fin m) : (transport g e rename).release a ↔ g.release (e.toOld a) := Iff.rfl
@[simp] theorem source (a : Fin m) :
    e.toOld ((transport g e rename).source a) = g.source (e.toOld a) := e.old_new _
@[simp] theorem value (a : Fin m) :
    ((transport g e rename).event a).effect.value = (g.event (e.toOld a)).effect.value := rfl
@[simp] theorem coherence (a b : Fin m) :
    (transport g e rename).coherence a b ↔ g.coherence (e.toOld a) (e.toOld b) := Iff.rfl
@[simp] theorem po (a b : Fin m) :
    (transport g e rename).po a b ↔ g.po (e.toOld a) (e.toOld b) := Iff.rfl

theorem sameAddress (injective : Function.Injective rename) (a b : Fin m) :
    (transport g e rename).sameAddress a b ↔ g.sameAddress (e.toOld a) (e.toOld b) := by
  exact ⟨fun h => injective h, congrArg rename⟩

theorem rf (a b : Fin m) :
    (transport g e rename).rf a b ↔ g.rf (e.toOld a) (e.toOld b) := by
  unfold Graph.rf
  rw [read, ← e.eq_iff, source]

theorem morallyStrong (injective : Function.Injective rename) (a b : Fin m) :
    (transport g e rename).morallyStrong a b ↔ g.morallyStrong (e.toOld a) (e.toOld b) := by
  simp only [Graph.morallyStrong, initial, sameAddress g e rename injective]

theorem observation (injective : Function.Injective rename) (a b : Fin m) :
    (transport g e rename).observation a b ↔ g.observation (e.toOld a) (e.toOld b) := by
  simp only [Graph.observation, rf, morallyStrong g e rename injective]

theorem releasePattern (injective : Function.Injective rename) (a b : Fin m) :
    (transport g e rename).releasePattern a b ↔ g.releasePattern (e.toOld a) (e.toOld b) := by
  simp only [Graph.releasePattern, release, write, initial, po,
    sameAddress g e rename injective, e.eq_iff]

theorem acquirePattern (injective : Function.Injective rename) (a b : Fin m) :
    (transport g e rename).acquirePattern a b ↔ g.acquirePattern (e.toOld a) (e.toOld b) := by
  simp only [Graph.acquirePattern, acquire, read, po,
    sameAddress g e rename injective, e.eq_iff]

theorem sync (injective : Function.Injective rename) (a b : Fin m) :
    (transport g e rename).sync a b ↔ g.sync (e.toOld a) (e.toOld b) := by
  simp only [Graph.sync, releasePattern g e rename injective,
    acquirePattern g e rename injective, observation g e rename injective,
    morallyStrong g e rename injective]
  constructor
  · rintro ⟨different, w, r, hw, hr, ho, hs⟩
    exact ⟨different, e.toOld w, e.toOld r, hw, hr, ho, hs⟩
  · rintro ⟨different, w, r, hw, hr, ho, hs⟩
    exact ⟨different, e.toNew w, e.toNew r, by simpa only [e.old_new] using hw,
      by simpa only [e.old_new] using hr, by simpa only [e.old_new] using ho, hs⟩

theorem baseEdge (injective : Function.Injective rename) (a b : Fin m) :
    (transport g e rename).baseEdge a b ↔ g.baseEdge (e.toOld a) (e.toOld b) := by
  simp only [Graph.baseEdge, po, sync g e rename injective]

theorem path_map (f : α → β) {r : α → α → Prop} {s : β → β → Prop}
    (edge : ∀ a b, r a b → s (f a) (f b)) (path : Path r a b) : Path s (f a) (f b) := by
  induction path with
  | edge h => exact .edge (edge _ _ h)
  | join _ _ left right => exact .join left right

theorem path_iff (r : Fin n → Fin n → Prop) (s : Fin m → Fin m → Prop)
    (edges : ∀ a b, s a b ↔ r (e.toOld a) (e.toOld b)) (a b : Fin m) :
    Path s a b ↔ Path r (e.toOld a) (e.toOld b) := by
  constructor
  · exact path_map e.toOld (fun x y => (edges x y).mp)
  · intro path
    have mapped := path_map e.toNew (s := s) (fun x y h =>
      (edges (e.toNew x) (e.toNew y)).mpr (by simpa only [e.old_new] using h)) path
    simpa only [e.new_old] using mapped

theorem base (injective : Function.Injective rename) (a b : Fin m) :
    (transport g e rename).base a b ↔ g.base (e.toOld a) (e.toOld b) :=
  path_iff e _ _ (baseEdge g e rename injective) a b

theorem proxyBase (injective : Function.Injective rename) (a b : Fin m) :
    (transport g e rename).proxyBase a b ↔ g.proxyBase (e.toOld a) (e.toOld b) := by
  simp only [Graph.proxyBase, base g e rename injective, sameAddress g e rename injective]

theorem cause (injective : Function.Injective rename) (a b : Fin m) :
    (transport g e rename).cause a b ↔ g.cause (e.toOld a) (e.toOld b) := by
  simp only [Graph.cause, proxyBase g e rename injective, observation g e rename injective]
  constructor
  · rintro (direct | ⟨z, observed, based⟩)
    · exact Or.inl direct
    · exact Or.inr ⟨e.toOld z, observed, based⟩
  · rintro (direct | ⟨z, observed, based⟩)
    · exact Or.inl direct
    · exact Or.inr ⟨e.toNew z, by simpa only [e.old_new] using observed,
        by simpa only [e.old_new] using based⟩

theorem communication (a b : Fin m) :
    (transport g e rename).communication a b ↔ g.communication (e.toOld a) (e.toOld b) := by
  simp only [Graph.communication, rf, coherence, read, source]

theorem locationEdge (injective : Function.Injective rename) (a b : Fin m) :
    (transport g e rename).locationEdge a b ↔ g.locationEdge (e.toOld a) (e.toOld b) := by
  simp only [Graph.locationEdge, po, sameAddress g e rename injective, communication,
    morallyStrong g e rename injective]

theorem locationPath (injective : Function.Injective rename) (a b : Fin m) :
    Path (transport g e rename).locationEdge a b ↔ Path g.locationEdge (e.toOld a) (e.toOld b) :=
  path_iff e _ _ (locationEdge g e rename injective) a b

private theorem sources_def (g : Graph n) : g.Sources ↔
    ∀ r, g.read r → g.write (g.source r) ∧ g.sameAddress (g.source r) r ∧
      (g.event (g.source r)).effect.value = (g.event r).effect.value :=
  ⟨fun h => h.compatible, fun h => ⟨h⟩⟩

theorem sources_iff (injective : Function.Injective rename) :
    (transport g e rename).Sources ↔ g.Sources := by
  simp only [sources_def, read, write, sameAddress g e rename injective, value, source]
  exact e.forall_old (fun r => g.read r → g.write (g.source r) ∧ g.sameAddress (g.source r) r ∧
    (g.event (g.source r)).effect.value = (g.event r).effect.value)

private theorem coherent_def (g : Graph n) : g.Coherent ↔
    (∀ a b, g.coherence a b → g.write a ∧ g.write b ∧ g.sameAddress a b) ∧
    (∀ a, ¬g.coherence a a) ∧
    (∀ a b c, g.coherence a b → g.coherence b c → g.coherence a c) ∧
    (∀ a b, g.write a → g.write b → g.sameAddress a b → a ≠ b →
      g.coherence a b ∨ g.coherence b a) ∧
    (∀ a b, g.initial a → g.write b → g.sameAddress a b → a ≠ b → g.coherence a b) := by
  constructor
  · intro h; exact ⟨h.typed, h.irrefl, h.trans, h.total, h.initFirst⟩
  · rintro ⟨typed, irrefl, trans, total, initFirst⟩
    exact ⟨typed, irrefl, trans, total, initFirst⟩

theorem coherent_iff (injective : Function.Injective rename) :
    (transport g e rename).Coherent ↔ g.Coherent := by
  simp only [coherent_def, coherence, write, initial, sameAddress g e rename injective,
    e.ne_iff]
  exact and_congr
    (e.forall_old_two (fun a b => g.coherence a b → g.write a ∧ g.write b ∧ g.sameAddress a b))
    (and_congr (e.forall_old (fun a => ¬g.coherence a a))
      (and_congr (e.forall_old_three (fun a b c => g.coherence a b → g.coherence b c → g.coherence a c))
        (and_congr (e.forall_old_two (fun a b => g.write a → g.write b → g.sameAddress a b →
          a ≠ b → g.coherence a b ∨ g.coherence b a))
          (e.forall_old_two (fun a b => g.initial a → g.write b → g.sameAddress a b → a ≠ b → g.coherence a b)))))

private theorem valid_def (g : Graph n) : g.Valid ↔ g.Sources ∧ g.Coherent ∧
    (∀ a, ¬g.base a a) ∧
    (∀ a b, g.write a → g.write b → g.sameAddress a b → g.cause a b → g.coherence a b) ∧
    (∀ r w, g.read r → g.write w → g.sameAddress r w → g.cause r w → g.source r ≠ w) ∧
    (∀ w r, g.write w → g.read r → g.sameAddress w r → g.cause w r → ¬g.coherence (g.source r) w) ∧
    (∀ a, ¬Path g.locationEdge a a) := by
  constructor
  · intro h; exact ⟨h.sources, h.co, h.base_irrefl, h.coherence_cause, h.no_future, h.no_stale, h.sc_per_location⟩
  · rintro ⟨sources, co, base_irrefl, coherence_cause, no_future, no_stale, sc_per_location⟩
    exact ⟨sources, co, base_irrefl, coherence_cause, no_future, no_stale, sc_per_location⟩

/-- Renaming neither discards nor creates a memory validity obligation. -/
theorem valid_iff (injective : Function.Injective rename) :
    (transport g e rename).Valid ↔ g.Valid := by
  simp only [valid_def, sources_iff g e rename injective, coherent_iff g e rename injective,
    read, write, sameAddress g e rename injective, cause g e rename injective,
    coherence, e.ne_iff, source, base g e rename injective, locationPath g e rename injective]
  exact and_congr Iff.rfl (and_congr Iff.rfl
    (and_congr (e.forall_old (fun a => ¬g.base a a))
      (and_congr (e.forall_old_two (fun a b => g.write a → g.write b → g.sameAddress a b →
        g.cause a b → g.coherence a b))
        (and_congr (e.forall_old_two (fun r w => g.read r → g.write w → g.sameAddress r w →
          g.cause r w → g.source r ≠ w))
          (and_congr (e.forall_old_two (fun w r => g.write w → g.read r → g.sameAddress w r →
            g.cause w r → ¬g.coherence (g.source r) w))
            (e.forall_old (fun a => ¬Path g.locationEdge a a)))))))

theorem ordered_base (injective : Function.Injective rename) (extra : Fin n → Fin n → Prop)
    (a b : Fin m) :
    Graph.Ordered.base (transport g e rename) (order e extra) a b ↔
      Graph.Ordered.base g extra (e.toOld a) (e.toOld b) := by
  apply path_iff e
  intro x y
  simp only [Graph.Ordered.baseEdge, baseEdge g e rename injective, order]

theorem ordered_cause (injective : Function.Injective rename) (extra : Fin n → Fin n → Prop)
    (a b : Fin m) :
    Graph.Ordered.cause (transport g e rename) (order e extra) a b ↔
      Graph.Ordered.cause g extra (e.toOld a) (e.toOld b) := by
  simp only [Graph.Ordered.cause, ordered_base g e rename injective,
    sameAddress g e rename injective, observation g e rename injective]
  constructor
  · rintro (direct | ⟨z, observed, based, same⟩)
    · exact Or.inl direct
    · exact Or.inr ⟨e.toOld z, observed, based, same⟩
  · rintro (direct | ⟨z, observed, based, same⟩)
    · exact Or.inl direct
    · exact Or.inr ⟨e.toNew z, by simpa only [e.old_new] using observed,
        by simpa only [e.old_new] using based, by simpa only [e.old_new] using same⟩

private theorem ordered_valid_def (g : Graph n) (extra : Fin n → Fin n → Prop) :
    Graph.Ordered.Valid g extra ↔ g.Sources ∧ g.Coherent ∧
    (∀ a, ¬Graph.Ordered.base g extra a a) ∧
    (∀ a b, g.write a → g.write b → g.sameAddress a b → Graph.Ordered.cause g extra a b → g.coherence a b) ∧
    (∀ r w, g.read r → g.write w → g.sameAddress r w → Graph.Ordered.cause g extra r w → g.source r ≠ w) ∧
    (∀ w r, g.write w → g.read r → g.sameAddress w r → Graph.Ordered.cause g extra w r → ¬g.coherence (g.source r) w) ∧
    (∀ a, ¬Path g.locationEdge a a) := by
  constructor
  · intro h; exact ⟨h.sources, h.co, h.base_irrefl, h.coherence_cause, h.no_future, h.no_stale, h.sc_per_location⟩
  · rintro ⟨sources, co, base_irrefl, coherence_cause, no_future, no_stale, sc_per_location⟩
    exact ⟨sources, co, base_irrefl, coherence_cause, no_future, no_stale, sc_per_location⟩

/-- Additional base-order edges are transported exactly, not inferred or added. -/
theorem ordered_valid_iff (injective : Function.Injective rename) (extra : Fin n → Fin n → Prop) :
    Graph.Ordered.Valid (transport g e rename) (order e extra) ↔ Graph.Ordered.Valid g extra := by
  simp only [ordered_valid_def, sources_iff g e rename injective, coherent_iff g e rename injective,
    read, write, sameAddress g e rename injective, ordered_cause g e rename injective,
    coherence, e.ne_iff, source, ordered_base g e rename injective, locationPath g e rename injective]
  exact and_congr Iff.rfl (and_congr Iff.rfl
    (and_congr (e.forall_old (fun a => ¬Graph.Ordered.base g extra a a))
      (and_congr (e.forall_old_two (fun a b => g.write a → g.write b → g.sameAddress a b →
        Graph.Ordered.cause g extra a b → g.coherence a b))
        (and_congr (e.forall_old_two (fun r w => g.read r → g.write w → g.sameAddress r w →
          Graph.Ordered.cause g extra r w → g.source r ≠ w))
          (and_congr (e.forall_old_two (fun w r => g.write w → g.read r → g.sameAddress w r →
            Graph.Ordered.cause g extra w r → ¬g.coherence (g.source r) w))
            (e.forall_old (fun a => ¬Path g.locationEdge a a)))))))

def renameAddresses (g : Graph n) (rename : Nat → Nat) : Graph n :=
  transport g (IndexEquiv.refl n) rename

def reindex (g : Graph n) (e : IndexEquiv n m) : Graph m := transport g e id

theorem renameAddresses_valid_iff (injective : Function.Injective rename) :
    (renameAddresses g rename).Valid ↔ g.Valid := valid_iff g _ rename injective

theorem renameAddresses_ordered_valid_iff (injective : Function.Injective rename)
    (extra : Fin n → Fin n → Prop) :
    Graph.Ordered.Valid (renameAddresses g rename) extra ↔ Graph.Ordered.Valid g extra :=
  ordered_valid_iff g (IndexEquiv.refl n) rename injective extra

theorem reindex_valid_iff : (reindex g e).Valid ↔ g.Valid :=
  valid_iff g e id (fun _ _ h => h)

theorem reindex_ordered_valid_iff (extra : Fin n → Fin n → Prop) :
    Graph.Ordered.Valid (reindex g e) (order e extra) ↔ Graph.Ordered.Valid g extra :=
  ordered_valid_iff g e id (fun _ _ h => h) extra

end Ptx.GraphTransport

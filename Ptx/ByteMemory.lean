import Ptx.ScopedMemory

/-! Byte observations for aligned fixed-size u32 accesses. Byte offset zero is
the least significant byte (the selected NVIDIA little-endian ABI convention). Address identity remains the
existing allocation-relative word index: this slice has no mixed-size overlap. -/
namespace Ptx

abbrev Byte := BitVec 8

/-- The byte at increasing address offset in a little-endian u32 word. -/
def wordByte (value : Word) (offset : Fin 4) : Byte :=
  BitVec.ofNat 8 (value.toNat / 2 ^ (8 * offset.val))

/-- Equality of all four constituent bytes determines the full u32 value. -/
theorem word_eq_of_bytes (left right : Word)
    (equal : ∀ offset, wordByte left offset = wordByte right offset) : left = right := by
  apply BitVec.eq_of_toNat_eq
  have h0 := congrArg BitVec.toNat (equal 0)
  have h1 := congrArg BitVec.toNat (equal 1)
  have h2 := congrArg BitVec.toNat (equal 2)
  have h3 := congrArg BitVec.toNat (equal 3)
  simp only [wordByte, BitVec.toNat_ofNat] at h0 h1 h2 h3
  change left.toNat / 1 % 256 = right.toNat / 1 % 256 at h0
  change left.toNat / 256 % 256 = right.toNat / 256 % 256 at h1
  change left.toNat / 65536 % 256 = right.toNat / 65536 % 256 at h2
  change left.toNat / 16777216 % 256 = right.toNat / 16777216 % 256 at h3
  have leftBound := left.isLt
  have rightBound := right.isLt
  omega



/-- The pinned ISA's observation wording does not resolve torn reads explicitly.
Both interpretations are exposed; neither is asserted to be uniquely authoritative. -/
inductive ObservationPolicy where
  | anyByte
  | wholeSource
  deriving DecidableEq, Repr

structure ByteGraph (n : Nat) where
  event : Fin n → Occurrence
  source : Fin n → Fin 4 → Fin n
  co : Fin n → Fin n → Bool
  topology : Nat → ThreadLocation
  scope : Fin n → Scope
  observationPolicy : ObservationPolicy

namespace ByteGraph

set_option synthInstance.maxSize 16384

/-- First-byte projection. It is a valid whole-word graph only under further
conditions; the byte model does not use this projection's source-based relations. -/
def toScoped (g : ByteGraph n) : ScopedGraph n :=
  ⟨⟨g.event, fun r => g.source r 0, g.co⟩, g.topology, g.scope⟩

abbrev read (g : ByteGraph n) := g.toScoped.graph.read
abbrev write (g : ByteGraph n) := g.toScoped.graph.write
abbrev initial (g : ByteGraph n) := g.toScoped.graph.initial
abbrev sameAddress (g : ByteGraph n) := g.toScoped.graph.sameAddress
abbrev coherence (g : ByteGraph n) := g.toScoped.graph.coherence
abbrev morallyStrong (g : ByteGraph n) := g.toScoped.morallyStrong

/-- §8.9.7 explicitly uses reading any byte. -/
def rf (g : ByteGraph n) (w r : Fin n) : Prop :=
  g.read r ∧ ∃ offset, g.source r offset = w

def readsWhole (g : ByteGraph n) (w r : Fin n) : Prop :=
  g.read r ∧ ∀ offset, g.source r offset = w

def observation (g : ByteGraph n) (w r : Fin n) : Prop :=
  (match g.observationPolicy with
   | .anyByte => g.rf w r
   | .wholeSource => g.readsWhole w r) ∧ g.morallyStrong w r

def sync (g : ByteGraph n) (a b : Fin n) : Prop :=
  (g.event a).thread ≠ (g.event b).thread ∧
    ∃ w r, g.toScoped.graph.releasePattern a w ∧ g.toScoped.graph.acquirePattern r b ∧
      g.observation w r ∧ g.morallyStrong a b

def baseEdge (g : ByteGraph n) (a b : Fin n) : Prop := g.toScoped.graph.po a b ∨ g.sync a b
def base (g : ByteGraph n) : Fin n → Fin n → Prop := Path g.baseEdge
def proxyBase (g : ByteGraph n) (a b : Fin n) : Prop := g.base a b ∧ g.sameAddress a b
def cause (g : ByteGraph n) (a b : Fin n) : Prop :=
  g.proxyBase a b ∨ ∃ z, g.observation a z ∧ g.proxyBase z b

def communication (g : ByteGraph n) (a b : Fin n) : Prop :=
  g.rf a b ∨ g.coherence a b ∨ (g.read a ∧ ∃ offset, g.coherence (g.source a offset) b)

def locationEdge (g : ByteGraph n) (a b : Fin n) : Prop :=
  (g.toScoped.graph.po a b ∧ g.sameAddress a b) ∨
    (g.communication a b ∧ g.morallyStrong a b)

structure Sources (g : ByteGraph n) : Prop where
  compatible : ∀ r, g.read r → ∀ offset,
    g.write (g.source r offset) ∧ g.sameAddress (g.source r offset) r ∧
      wordByte (g.event (g.source r offset)).effect.value offset =
        wordByte (g.event r).effect.value offset

/-- §8.10.3: a read morally strong with W cannot combine a byte from W with
another byte from a coherence predecessor of W. This does not say all sources agree. -/
def SingleCopy (g : ByteGraph n) : Prop :=
  ∀ r w, g.read r → g.write w → g.morallyStrong r w →
    ∀ offset, g.source r offset = w → ∀ other, ¬g.coherence (g.source r other) w

/-- Scope-aware coherence uses the byte-derived causality relation. -/
structure Coherent (g : ByteGraph n) : Prop where
  typed : ∀ a b, g.coherence a b → g.write a ∧ g.write b ∧ g.sameAddress a b
  irrefl : ∀ a, ¬g.coherence a a
  trans : ∀ a b c, g.coherence a b → g.coherence b c → g.coherence a c
  total : ∀ a b, g.write a → g.write b → g.morallyStrong a b → a ≠ b →
    g.coherence a b ∨ g.coherence b a
  initFirst : ∀ a b, g.initial a → g.write b → g.sameAddress a b → a ≠ b → g.coherence a b
  justified : ∀ a b, g.coherence a b →
    g.initial a ∨ g.initial b ∨ g.morallyStrong a b ∨ g.cause a b ∨ g.cause b a

/-- Byte-source constraints for fixed-size dependency-free memory events.
NTA for arbitrary dependent concurrent programs is not provided by this predicate. -/
structure Valid (g : ByteGraph n) : Prop where
  sources : g.Sources
  co : g.Coherent
  atomicity : g.SingleCopy
  base_irrefl : ∀ a, ¬g.base a a
  coherence_cause : ∀ a b, g.write a → g.write b → g.sameAddress a b →
    g.cause a b → g.coherence a b
  no_future : ∀ r w, g.read r → g.write w → g.sameAddress r w →
    g.cause r w → ∀ offset, g.source r offset ≠ w
  no_stale : ∀ w r, g.write w → g.read r → g.sameAddress w r →
    g.cause w r → ∀ offset, ¬g.coherence (g.source r offset) w
  sc_per_location : ∀ a, ¬Path g.locationEdge a a

/-- Source uniformity, not mere equality of numerical results. Non-read entries
in the source function have no semantic role and need not be uniform. -/
def Uniform (g : ByteGraph n) : Prop :=
  ∀ r, g.read r → ∀ offset, g.source r offset = g.source r 0

instance (g : ByteGraph n) (a b : Fin n) : Decidable (g.rf a b) := by unfold rf; infer_instance
instance (g : ByteGraph n) (a b : Fin n) : Decidable (g.readsWhole a b) := by unfold readsWhole; infer_instance
instance (g : ByteGraph n) (a b : Fin n) : Decidable (g.observation a b) := by
  unfold observation; cases g.observationPolicy <;> infer_instance
instance (g : ByteGraph n) (a b : Fin n) : Decidable (g.sync a b) := by unfold sync; infer_instance
instance (g : ByteGraph n) (a b : Fin n) : Decidable (g.baseEdge a b) := by unfold baseEdge; infer_instance
instance (g : ByteGraph n) (a b : Fin n) : Decidable (g.base a b) :=
  decidable_of_iff (reachable (fun x y => decide (g.baseEdge x y)) a b = true)
    (by simpa [base] using reachable_iff (fun x y => decide (g.baseEdge x y)) a b)
instance (g : ByteGraph n) (a b : Fin n) : Decidable (g.proxyBase a b) := by unfold proxyBase; infer_instance
instance (g : ByteGraph n) (a b : Fin n) : Decidable (g.cause a b) := by unfold cause; infer_instance
instance (g : ByteGraph n) (a b : Fin n) : Decidable (g.communication a b) := by unfold communication; infer_instance
instance (g : ByteGraph n) (a b : Fin n) : Decidable (g.locationEdge a b) := by unfold locationEdge; infer_instance
instance (g : ByteGraph n) (a b : Fin n) : Decidable (Path g.locationEdge a b) :=
  decidable_of_iff (reachable (fun x y => decide (g.locationEdge x y)) a b = true)
    (by simpa using reachable_iff (fun x y => decide (g.locationEdge x y)) a b)
instance (g : ByteGraph n) : Decidable g.Sources :=
  decidable_of_iff (∀ r, g.read r → ∀ offset,
    g.write (g.source r offset) ∧ g.sameAddress (g.source r offset) r ∧
      wordByte (g.event (g.source r offset)).effect.value offset = wordByte (g.event r).effect.value offset)
    ⟨Sources.mk, Sources.compatible⟩
instance (g : ByteGraph n) : Decidable g.SingleCopy := by unfold SingleCopy; infer_instance
instance (g : ByteGraph n) : Decidable g.Uniform := by unfold Uniform; infer_instance

instance (g : ByteGraph n) : Decidable g.Coherent :=
  decidable_of_iff
    ((∀ a b, g.coherence a b → g.write a ∧ g.write b ∧ g.sameAddress a b) ∧
     (∀ a, ¬g.coherence a a) ∧
     (∀ a b c, g.coherence a b → g.coherence b c → g.coherence a c) ∧
     (∀ a b, g.write a → g.write b → g.morallyStrong a b → a ≠ b → g.coherence a b ∨ g.coherence b a) ∧
     (∀ a b, g.initial a → g.write b → g.sameAddress a b → a ≠ b → g.coherence a b) ∧
     (∀ a b, g.coherence a b → g.initial a ∨ g.initial b ∨ g.morallyStrong a b ∨ g.cause a b ∨ g.cause b a))
    ⟨fun ⟨a,b,c,d,e,f⟩ => ⟨a,b,c,d,e,f⟩, fun h => ⟨h.typed,h.irrefl,h.trans,h.total,h.initFirst,h.justified⟩⟩

instance (g : ByteGraph n) : Decidable g.Valid :=
  decidable_of_iff
    (g.Sources ∧ g.Coherent ∧ g.SingleCopy ∧ (∀ a, ¬g.base a a) ∧
     (∀ a b, g.write a → g.write b → g.sameAddress a b → g.cause a b → g.coherence a b) ∧
     (∀ r w, g.read r → g.write w → g.sameAddress r w → g.cause r w → ∀ offset, g.source r offset ≠ w) ∧
     (∀ w r, g.write w → g.read r → g.sameAddress w r → g.cause w r →
        ∀ offset, ¬g.coherence (g.source r offset) w) ∧
     (∀ a, ¬Path g.locationEdge a a))
    ⟨fun ⟨a,b,c,d,e,f,h,i⟩ => ⟨a,b,c,d,e,f,h,i⟩,
      fun h => ⟨h.sources,h.co,h.atomicity,h.base_irrefl,h.coherence_cause,h.no_future,h.no_stale,h.sc_per_location⟩⟩



variable {g : ByteGraph n}

theorem rf_projection (uniform : g.Uniform) : g.rf w r ↔ g.toScoped.graph.rf w r := by
  constructor
  · rintro ⟨hr, offset, source⟩
    exact ⟨hr, (uniform r hr offset).symm.trans source⟩
  · rintro ⟨hr, source⟩
    exact ⟨hr, 0, source⟩

theorem readsWhole_projection (uniform : g.Uniform) :
    g.readsWhole w r ↔ g.toScoped.graph.rf w r := by
  constructor
  · rintro ⟨hr, source⟩
    exact ⟨hr, source 0⟩
  · rintro ⟨hr, source⟩
    exact ⟨hr, fun offset => (uniform r hr offset).trans source⟩

theorem observation_projection (uniform : g.Uniform) :
    g.observation w r ↔ g.toScoped.observation w r := by
  cases hp : g.observationPolicy <;>
    simp [observation, hp, ScopedGraph.observation, rf_projection uniform, readsWhole_projection uniform,
      morallyStrong]

theorem sync_projection (uniform : g.Uniform) : g.sync a b ↔ g.toScoped.sync a b := by
  simp [sync, ScopedGraph.sync, observation_projection uniform, toScoped, morallyStrong]

theorem base_projection (uniform : g.Uniform) : g.base a b ↔ g.toScoped.base a b := by
  have edges : g.baseEdge = g.toScoped.baseEdge := by
    funext x y
    exact propext (by simp [baseEdge, ScopedGraph.baseEdge, sync_projection uniform])
  simp only [base, ScopedGraph.base, edges]

theorem cause_projection (uniform : g.Uniform) : g.cause a b ↔ g.toScoped.cause a b := by
  simp [cause, ScopedGraph.cause, proxyBase, ScopedGraph.proxyBase,
    base_projection uniform, observation_projection uniform, sameAddress]

theorem communication_projection (uniform : g.Uniform) :
    g.communication a b ↔ g.toScoped.graph.communication a b := by
  by_cases hr : g.read a
  · simp [communication, Graph.communication, rf_projection uniform, hr,
      uniform a hr, coherence] <;> rfl
  · simp [communication, Graph.communication, rf_projection uniform, hr, read]

theorem location_projection (uniform : g.Uniform) :
    Path g.locationEdge a b ↔ Path g.toScoped.locationEdge a b := by
  have edges : g.locationEdge = g.toScoped.locationEdge := by
    funext x y
    exact propext (by simp [locationEdge, ScopedGraph.locationEdge,
      communication_projection uniform, morallyStrong, sameAddress])
  rw [edges]

/-- Uniform source identity supplies full word-value equality through byte extensionality. -/
theorem sources_projection (uniform : g.Uniform) : g.Sources ↔ g.toScoped.graph.Sources := by
  constructor
  · intro h
    constructor
    intro r hr
    obtain ⟨hw, ha, _⟩ := h.compatible r hr 0
    refine ⟨hw, ha, word_eq_of_bytes _ _ ?_⟩
    intro offset
    have hb := (h.compatible r hr offset).2.2
    rw [uniform r hr offset] at hb
    exact hb
  · intro h
    constructor
    intro r hr offset
    rw [uniform r hr offset]
    have hb := h.compatible r hr
    exact ⟨hb.1, hb.2.1, congrArg (fun value => wordByte value offset) hb.2.2⟩

theorem coherent_projection (uniform : g.Uniform) : g.Coherent ↔ g.toScoped.Coherent := by
  constructor
  · intro h
    refine ⟨h.typed,h.irrefl,h.trans,h.total,h.initFirst,?_⟩
    intro a b hc
    simpa only [cause_projection uniform] using h.justified a b hc
  · intro h
    refine ⟨h.typed,h.irrefl,h.trans,h.total,h.initFirst,?_⟩
    intro a b hc
    simpa only [cause_projection uniform] using h.justified a b hc

/-- Exact model equivalence under source uniformity, for either observation policy.
This does not infer uniform sources from equal read/write numerical values. -/
theorem projection_valid_iff (uniform : g.Uniform) : g.Valid ↔ g.toScoped.Valid := by
  constructor
  · intro h
    exact {
      sources := (sources_projection uniform).mp h.sources
      co := (coherent_projection uniform).mp h.co
      base_irrefl := fun a hp => h.base_irrefl a ((base_projection uniform).mpr hp)
      coherence_cause := fun a b hw hw' ha hc =>
        h.coherence_cause a b hw hw' ha ((cause_projection uniform).mpr hc)
      no_future := fun r w hr hw ha hc =>
        h.no_future r w hr hw ha ((cause_projection uniform).mpr hc) 0
      no_stale := fun w r hw hr ha hc =>
        h.no_stale w r hw hr ha ((cause_projection uniform).mpr hc) 0
      sc_per_location := fun a hp => h.sc_per_location a ((location_projection uniform).mpr hp)
    }
  · intro h
    refine {
      sources := (sources_projection uniform).mpr h.sources
      co := (coherent_projection uniform).mpr h.co
      atomicity := ?_
      base_irrefl := fun a hp => h.base_irrefl a ((base_projection uniform).mp hp)
      coherence_cause := fun a b hw hw' ha hc =>
        h.coherence_cause a b hw hw' ha ((cause_projection uniform).mp hc)
      no_future := ?_
      no_stale := ?_
      sc_per_location := fun a hp => h.sc_per_location a ((location_projection uniform).mp hp)
    }
    · intro r w hr _ _ offset source other
      rw [uniform r hr offset] at source
      rw [uniform r hr other, source]
      exact h.co.irrefl w
    · intro r w hr hw ha hc offset
      rw [uniform r hr offset]
      exact h.no_future r w hr hw ha ((cause_projection uniform).mp hc)
    · intro w r hw hr ha hc offset
      rw [uniform r hr offset]
      exact h.no_stale w r hw hr ha ((cause_projection uniform).mp hc)

/-- Canonical embedding: every byte gets the previous model's one source. -/
def ofScoped (policy : ObservationPolicy) (g : ScopedGraph n) : ByteGraph n :=
  ⟨g.graph.event, fun r _ => g.graph.source r, g.graph.co, g.topology, g.scope, policy⟩

theorem ofScoped_uniform (policy : ObservationPolicy) (g : ScopedGraph n) :
    (ofScoped policy g).Uniform := fun _ _ _ => rfl

/-- The existing non-torn scoped semantics embeds without losing or adding executions. -/
theorem ofScoped_valid_iff (policy : ObservationPolicy) (g : ScopedGraph n) :
    (ofScoped policy g).Valid ↔ g.Valid :=
  projection_valid_iff (ofScoped_uniform policy g)

theorem uniform_policy_independent (uniform : g.Uniform) (first second : ObservationPolicy) :
    {g with observationPolicy := first}.Valid ↔ {g with observationPolicy := second}.Valid := by
  rw [projection_valid_iff (g := {g with observationPolicy := first}) (by exact uniform),
      projection_valid_iff (g := {g with observationPolicy := second}) (by exact uniform)]
  rfl



/-- Initialization cannot be later than an overlapping write in a coherent graph. -/
theorem coherence_later_not_initial (coherent : g.Coherent) (edge : g.coherence a b) :
    ¬g.initial b := by
  intro initial
  have typed := coherent.typed a b edge
  have different : b ≠ a := by
    intro same
    subst b
    exact coherent.irrefl a edge
  have reverse := coherent.initFirst b a initial typed.1 typed.2.2.symm different
  exact coherent.irrefl a (coherent.trans a b a edge reverse)

/-- A sufficient uniformity criterion: chosen sources are coherence-comparable,
and this read is morally strong with every chosen non-initial write. The proof
uses qualified atomicity; initialization is handled by its explicit earliest order. -/
theorem sources_uniform_at (valid : g.Valid) (r : Fin n) (hr : g.read r)
    (moral : ∀ offset, ¬g.initial (g.source r offset) → g.morallyStrong r (g.source r offset))
    (comparable : ∀ first second, g.source r first ≠ g.source r second →
      g.coherence (g.source r first) (g.source r second) ∨
      g.coherence (g.source r second) (g.source r first)) :
    ∀ offset, g.source r offset = g.source r 0 := by
  intro offset
  by_cases different : g.source r offset = g.source r 0
  · exact different
  exfalso
  rcases comparable offset 0 different with forward | backward
  · exact valid.atomicity r (g.source r 0) hr (valid.sources.compatible r hr 0).1
      (moral 0 (coherence_later_not_initial valid.co forward)) 0 rfl offset forward
  · exact valid.atomicity r (g.source r offset) hr (valid.sources.compatible r hr offset).1
      (moral offset (coherence_later_not_initial valid.co backward)) offset rfl 0 backward

/-- Mutual scope coverage derives source uniformity from qualified atomicity;
it is not an additional assumption of the original all-in-scope fragment. -/
theorem uniform_of_all_in_scope (valid : g.Valid) (inScope : g.toScoped.AllInScope) :
    g.Uniform := by
  intro r hr
  apply sources_uniform_at valid r hr
  · intro offset noninitial
    apply (ScopedGraph.morallyStrong_legacy inScope).mpr
    refine ⟨?_,noninitial,(valid.sources.compatible r hr offset).2.1.symm⟩
    intro isInitial
    change (g.toScoped.graph.event r).effect.op = .init at isInitial
    simp [read, Graph.read, isInitial] at hr
  · intro first second different
    have left := valid.sources.compatible r hr first
    have right := valid.sources.compatible r hr second
    have same : g.sameAddress (g.source r first) (g.source r second) :=
      left.2.1.trans right.2.1.symm
    by_cases initialLeft : g.initial (g.source r first)
    · exact Or.inl (valid.co.initFirst _ _ initialLeft right.1 same different)
    by_cases initialRight : g.initial (g.source r second)
    · exact Or.inr (valid.co.initFirst _ _ initialRight left.1 same.symm different.symm)
    exact valid.co.total _ _ left.1 right.1
      ((ScopedGraph.morallyStrong_legacy inScope).mpr ⟨initialLeft,initialRight,same⟩) different

/-- Under original mutual scope coverage, byte validity is exactly uniform
sources together with validity in the unchanged legacy whole-word model. -/
theorem all_in_scope_valid_iff (inScope : g.toScoped.AllInScope) :
    g.Valid ↔ g.Uniform ∧ g.toScoped.graph.Valid := by
  constructor
  · intro valid
    have uniform := uniform_of_all_in_scope valid inScope
    exact ⟨uniform,(ScopedGraph.valid_legacy inScope).mp ((projection_valid_iff uniform).mp valid)⟩
  · rintro ⟨uniform,valid⟩
    exact (projection_valid_iff uniform).mpr ((ScopedGraph.valid_legacy inScope).mpr valid)

end ByteGraph

/-- Byte-source choices decorate the existing actual constant-store program trace. -/
def Program.byteGraph (p : Program) (registers : Nat → Registers) (oracle : Nat → Nat → Word)
    (source : Fin (p.events registers oracle).length → Fin 4 → Fin (p.events registers oracle).length)
    (co : Fin (p.events registers oracle).length → Fin (p.events registers oracle).length → Bool)
    (topology : Nat → ThreadLocation) (scope : Fin (p.events registers oracle).length → Scope)
    (policy : ObservationPolicy) : ByteGraph (p.events registers oracle).length :=
  ⟨fun index => (p.events registers oracle).get index, source, co, topology, scope, policy⟩

/-- The same normalized constant-store fragment; target eligibility and allocation
contracts remain separate. The observation convention is an explicit argument. -/
def Program.ByteAdmitted (p : Program) (registers : Nat → Registers) (oracle : Nat → Nat → Word)
    (source : Fin (p.events registers oracle).length → Fin 4 → Fin (p.events registers oracle).length)
    (co : Fin (p.events registers oracle).length → Fin (p.events registers oracle).length → Bool)
    (topology : Nat → ThreadLocation) (scope : Fin (p.events registers oracle).length → Scope)
    (policy : ObservationPolicy) : Prop :=
  p.Bounded ∧ p.TopologyWellFormed topology ∧
    (p.byteGraph registers oracle source co topology scope policy).Valid

theorem Program.byteGraph_access_safe (p : Program)
    {registers : Nat → Registers} {oracle : Nat → Nat → Word}
    {source : Fin (p.events registers oracle).length → Fin 4 → Fin (p.events registers oracle).length}
    {co : Fin (p.events registers oracle).length → Fin (p.events registers oracle).length → Bool}
    {topology : Nat → ThreadLocation} {scope : Fin (p.events registers oracle).length → Scope}
    {policy : ObservationPolicy} (bounded : p.Bounded)
    (index : Fin (p.events registers oracle).length) :
    AccessSafe p.initial.length
      ((p.byteGraph registers oracle source co topology scope policy).event index).effect := by
  exact p.access_safe bounded (List.get_mem _ _)

end Ptx

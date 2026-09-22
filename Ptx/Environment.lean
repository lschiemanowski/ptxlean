import Ptx.Language

/-! Explicit topology, scalar storage contracts, and instruction eligibility.
Scope is not an access permission. Addresses are resolved allocation-relative
byte addresses; alias resolution and runtime allocation are external contracts. -/
namespace Ptx

/-- Abstract identities: CTA names are cluster-qualified, not raw `%ctaid` values. -/
structure ThreadLocation where
  device : Nat
  grid : Nat
  cluster : Nat
  cta : Nat
  thread : Nat
  deriving DecidableEq, Repr

def ThreadLocation.sameCluster (a b : ThreadLocation) : Bool :=
  a.device == b.device && a.grid == b.grid && a.cluster == b.cluster

def ThreadLocation.sameCTA (a b : ThreadLocation) : Bool :=
  a.sameCluster b && a.cta == b.cta

inductive Scope where
  | cta | cluster | gpu | sys
  deriving DecidableEq, Repr

/-- Device participants of one host program. Host thread execution is not modeled. -/
def Scope.includes (scope : Scope) (issuer participant : ThreadLocation) : Bool :=
  match scope with
  | .cta => issuer.sameCTA participant
  | .cluster => issuer.sameCluster participant
  | .gpu => issuer.device == participant.device
  | .sys => true

@[simp] theorem Scope.includes_self (scope : Scope) (thread : ThreadLocation) :
    scope.includes thread thread = true := by
  cases scope <;> simp [Scope.includes, ThreadLocation.sameCTA, ThreadLocation.sameCluster]

theorem Scope.cta_includes_cluster (h : Scope.cta.includes a b = true) :
    Scope.cluster.includes a b = true := by
  simp only [Scope.includes, ThreadLocation.sameCTA, Bool.and_eq_true] at h
  exact h.1

theorem Scope.cluster_includes_gpu (h : Scope.cluster.includes a b = true) :
    Scope.gpu.includes a b = true := by
  simp only [Scope.includes, ThreadLocation.sameCluster, Bool.and_eq_true] at h ⊢
  exact h.1.1

inductive AddressSpace where
  | global | shared | local | param
  deriving DecidableEq, Repr

structure Address where
  space : AddressSpace
  allocation : Nat
  offset : Nat
  deriving DecidableEq, Repr

inductive AccessKind where
  | read | write
  deriving DecidableEq, Repr

inductive StorageOwner where
  | system
  | device (id : Nat)
  | grid (device grid : Nat)
  | cta (location : ThreadLocation)
  | thread (location : ThreadLocation)
  deriving DecidableEq, Repr

structure Allocation where
  space : AddressSpace
  bytes : Nat
  alignment : Nat
  owner : StorageOwner
  readable : Bool
  writable : Bool
  initialized : Bool
  deriving DecidableEq, Repr

/-- Ownership validity prevents an arbitrary owner tag from broadening a state space. -/
def Allocation.ownerAllows (allocation : Allocation) (thread : ThreadLocation)
    (clusterAccess : Bool := false) : Bool :=
  match allocation.space, allocation.owner with
  | .global, .system => true
  | .global, .device device => thread.device == device
  | .shared, .cta owner =>
      if clusterAccess then thread.sameCluster owner else thread.sameCTA owner
  | .local, .thread owner => thread == owner
  | .param, .grid device grid => thread.device == device && thread.grid == grid
  | _, _ => false

structure Environment where
  allocations : Nat → Option Allocation

inductive AccessError where
  | unallocated | wrongSpace | inaccessible | outOfBounds | misaligned
  | permission | uninitialized | invalidWidth
  deriving DecidableEq, Repr

/-- `initialized` certifies the entire allocation, not an implicit zero fill.
An `uninitialized` result means this contract lacks known contents; PTX itself
allows unknown initial values. These diagnostics are contract failures, not a
classification of every PTX undefined/illegal behavior. Allocation alignment is
a supplied base-alignment guarantee. For shared cluster access the caller must
also supply the active-peer lifetime contract. -/
def Environment.checkAccess (environment : Environment) (thread : ThreadLocation)
    (kind : AccessKind) (address : Address) (width : Nat)
    (clusterAccess : Bool := false) : Except AccessError Unit :=
  match environment.allocations address.allocation with
  | none => .error .unallocated
  | some allocation =>
    if allocation.space != address.space then .error .wrongSpace
    else if !allocation.ownerAllows thread clusterAccess then .error .inaccessible
    else if width == 0 then .error .invalidWidth
    else if address.offset + width > allocation.bytes then .error .outOfBounds
    else if allocation.alignment % width != 0 || allocation.alignment == 0 ||
        address.offset % width != 0 then .error .misaligned
    else if kind == .read then
      if !allocation.readable then .error .permission
      else if !allocation.initialized then .error .uninitialized
      else .ok ()
    else if !allocation.writable || address.space == .param then .error .permission
    else .ok ()

def Environment.accessible (environment : Environment) (thread : ThreadLocation)
    (kind : AccessKind) (address : Address) (width : Nat)
    (clusterAccess : Bool := false) : Prop :=
  environment.checkAccess thread kind address width clusterAccess = .ok ()

instance (environment : Environment) (thread : ThreadLocation) (kind : AccessKind)
    (address : Address) (width : Nat) (clusterAccess : Bool) :
    Decidable (environment.accessible thread kind address width clusterAccess) := by
  unfold Environment.accessible
  cases environment.checkAccess thread kind address width clusterAccess with
  | error e => exact isFalse (by intro h; cases h)
  | ok value => cases value; exact isTrue rfl

/-- Successful checking entails ownership, complete byte bounds, and alignment. -/
theorem Environment.accessible_contract (environment : Environment) (thread : ThreadLocation)
    (kind : AccessKind) (address : Address) (width : Nat) (clusterAccess : Bool)
    (h : environment.accessible thread kind address width clusterAccess) :
    ∃ allocation, environment.allocations address.allocation = some allocation ∧
      allocation.space = address.space ∧ allocation.ownerAllows thread clusterAccess = true ∧
      0 < width ∧ address.offset + width ≤ allocation.bytes ∧
      0 < allocation.alignment ∧ allocation.alignment % width = 0 ∧ address.offset % width = 0 := by
  unfold Environment.accessible Environment.checkAccess at h
  cases ha : environment.allocations address.allocation with
  | none => simp [ha] at h
  | some allocation =>
    simp only [ha] at h
    simp at h
    repeat' (first | split at h | contradiction)
    all_goals refine ⟨allocation,rfl,?_,?_,?_,?_,?_,?_,?_⟩
    all_goals first | assumption | omega | simp_all

theorem Environment.accessible_bounds (environment : Environment) (thread : ThreadLocation)
    (kind : AccessKind) (address : Address) (width : Nat) (clusterAccess : Bool)
    (h : environment.accessible thread kind address width clusterAccess) :
    ∃ allocation, environment.allocations address.allocation = some allocation ∧
      address.offset + width ≤ allocation.bytes ∧ address.offset % width = 0 := by
  obtain ⟨allocation,ha,_,_,_,hb,_,_,halign⟩ := environment.accessible_contract thread kind address width clusterAccess h
  exact ⟨allocation,ha,hb,halign⟩

structure Target where
  /-- Major times ten plus minor for versions represented by this fragment. -/
  isa : Nat
  sm : Nat
  deriving DecidableEq, Repr

/-- Scalar 32-bit explicit-state-space forms only. `none` means default weak,
not an explicit `.weak` qualifier. Ordering direction is supplied by load/store syntax. -/
structure MemoryForm where
  kind : AccessKind
  space : AddressSpace
  scope : Option Scope
  sharedCluster : Bool := false
  deriving DecidableEq, Repr

inductive Eligibility where
  | supported
  | illegal (reason : String)
  | unsupported (reason : String)
  deriving DecidableEq, Repr

/-- §9.7.10.8/11 version and target notes. This is not a PTX parser. -/
def memoryEligibility (target : Target) (form : MemoryForm) : Eligibility :=
  if target.isa > 94 then .unsupported "ISA versions after pinned PTX 9.4"
  else if target.isa < 10 || target.sm < 10 then .illegal "scalar ld/st require PTX 1.0"
  else if form.sharedCluster && form.space != .shared then .illegal "::cluster requires shared space"
  else if form.scope.isSome && form.space != .global && form.space != .shared then
    .illegal "scoped relaxed/acquire/release require global or shared space"
  else if form.scope.isSome && (target.isa < 60 || target.sm < 70) then
    .illegal "scoped relaxed/acquire/release require PTX 6.0 and sm_70"
  else if (form.scope == some .cluster || form.sharedCluster) &&
      (target.isa < 78 || target.sm < 90) then
    .illegal "cluster scope/addressing require PTX 7.8 and sm_90"
  else if form.space == .param && form.kind == .write then
    .unsupported "device-function parameter ABI and st.param are not modeled"
  else .supported

end Ptx

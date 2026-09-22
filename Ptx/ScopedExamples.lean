import Ptx.ScopedMemory
import Ptx.MessagePassing

namespace Ptx.ScopedExamples

open MessagePassing
set_option synthInstance.maxSize 16384
set_option maxRecDepth 4096

/-- CTA identifiers are qualified by grid and cluster; both threads share a device. -/
def separateCTA (tid : Nat) : ThreadLocation := ⟨0,0,0,tid,0⟩
def sameCTA (tid : Nat) : ThreadLocation := ⟨0,0,0,0,tid⟩
def differentGrid (tid : Nat) : ThreadLocation := ⟨0,tid,0,0,0⟩
def uniform (scope : Scope) : Fin 6 → Scope := fun _ => scope

def candidate (flag payload : Word) (source : Fin 6 → Fin 6)
    (co : Fin 6 → Fin 6 → Bool) (topology : Nat → ThreadLocation)
    (scopes : Fin 6 → Scope) : ScopedGraph 6 :=
  (program .acquire).scopedGraph registers (oracle flag payload) source co topology scopes

/-- Publication needs mutual inclusion of the release/acquire endpoints, rather
than requiring every unrelated operation to have the same scope. -/
theorem publication (payload : Word) (source co) (topology : Nat → ThreadLocation)
    (scopes : Fin 6 → Scope)
    (valid : (candidate 1 payload source co topology scopes).Valid)
    (included : (candidate 1 payload source co topology scopes).mutualScope b c = true) :
    payload = 7 := by
  let g := candidate 1 payload source co topology scopes
  have flagSource : source c = b := by
    have h := valid.sources.compatible c (by trivial)
    change g.graph.write (source c) ∧ g.graph.sameAddress (source c) c ∧
      (g.graph.event (source c)).effect.value = 1 at h
    have cases : source c = 0 ∨ source c = 1 ∨ source c = 2 ∨
        source c = 3 ∨ source c = 4 ∨ source c = 5 := by omega
    rcases cases with h' | h' | h' | h' | h' | h'
    · rw [h'] at h
      have bad : (0 : Word) = 1 := h.2.2
      contradiction
    · rw [h'] at h
      have bad : (0 : Word) = 1 := h.2.2
      contradiction
    · rw [h'] at h
      have bad : (0 : Nat) = 1 := h.2.1
      omega
    · exact h'
    · rw [h'] at h; exact False.elim h.1
    · rw [h'] at h; exact False.elim h.1
  have moral : g.morallyStrong b c :=
    ⟨(by intro h; cases h), (by intro h; cases h), rfl, Or.inr (Or.inr included)⟩
  have synchronizes : g.sync b c :=
    ⟨by change some 0 ≠ some 1; decide,
      b,c,Or.inl ⟨rfl,rfl⟩,Or.inl ⟨rfl,rfl⟩,⟨⟨by trivial,flagSource⟩,moral⟩,moral⟩
  have poab : g.graph.po a b := ⟨(by intro h; cases h),rfl,Nat.zero_lt_one⟩
  have pocd : g.graph.po c d := ⟨(by intro h; cases h),rfl,Nat.zero_lt_one⟩
  have ordered : g.base a d :=
    .join (.edge (Or.inl poab))
      (.join (.edge (Or.inr synchronizes))
        (.edge (Or.inl pocd)))
  have causes : g.cause a d := Or.inl ⟨ordered,rfl⟩
  have notInitial : source d ≠ ip := by
    intro hs
    have hc := valid.co.initFirst ip a rfl (by trivial) rfl (by decide)
    exact valid.no_stale a d (by trivial) (by trivial) rfl causes
      (by change g.graph.coherence (source d) a; rw [hs]; exact hc)
  have h := valid.sources.compatible d (by trivial)
  change g.graph.write (source d) ∧ g.graph.sameAddress (source d) d ∧
    (g.graph.event (source d)).effect.value = payload at h
  have cases : source d = 0 ∨ source d = 1 ∨ source d = 2 ∨
      source d = 3 ∨ source d = 4 ∨ source d = 5 := by omega
  rcases cases with h' | h' | h' | h' | h' | h'
  · exact False.elim (notInitial h')
  · rw [h'] at h
    have bad : (1 : Nat) = 0 := h.2.1
    omega
  · rw [h'] at h; exact h.2.2.symm
  · rw [h'] at h
    have bad : (1 : Nat) = 0 := h.2.1
    omega
  · rw [h'] at h; exact False.elim h.1
  · rw [h'] at h; exact False.elim h.1

theorem gpu_all_in_scope (flag payload : Word) (source co) :
    (candidate flag payload source co separateCTA (uniform .gpu)).AllInScope := by
  intro a b ha hb
  have cases (i : Fin 6) : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 := by omega
  rcases cases a with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases cases b with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first | exact False.elim (ha rfl) | exact False.elim (hb rfl) | rfl

/-- Checked equality of validity predicates for every word/source/coherence choice. -/
theorem gpu_specialization (flag payload : Word) (source co) :
    (candidate flag payload source co separateCTA (uniform .gpu)).Valid ↔
      (MessagePassing.graph .acquire flag payload source co).Valid :=
  ScopedGraph.valid_legacy (gpu_all_in_scope flag payload source co)

theorem in_scope_execution_exists :
    (program .acquire).ScopedAdmitted registers (oracle 1 7) successSource witnessCo
      sameCTA (uniform .cta) ∧ result .acquire 1 7 = (1,7) := by
  refine ⟨⟨?_, ?_, ?_⟩,rfl⟩
  · simp [Program.Bounded, program, producer, consumer, Instr.address]
  · intro i _ j _ h; exact congrArg ThreadLocation.thread h
  · change (candidate 1 7 successSource witnessCo sameCTA (uniform .cta)).Valid
    decide

/-- Same acquire/release instructions; different CTA scopes admit the stale payload. -/
theorem outside_scope_execution_exists :
    (program .acquire).ScopedAdmitted registers (oracle 1 0) staleSource witnessCo
      separateCTA (uniform .cta) ∧ result .acquire 1 0 = (1,0) := by
  refine ⟨⟨?_, ?_, ?_⟩,rfl⟩
  · simp [Program.Bounded, program, producer, consumer, Instr.address]
  · intro i _ j _ h; exact congrArg ThreadLocation.cta h
  · change (candidate 1 0 staleSource witnessCo separateCTA (uniform .cta)).Valid
    decide

theorem outside_scope_no_sync :
    ¬(candidate 1 0 staleSource witnessCo separateCTA (uniform .cta)).sync b c := by decide

/-- One wide scope does not repair the other endpoint's narrow scope. -/
theorem scope_inclusion_is_mutual :
    (candidate 1 0 staleSource witnessCo separateCTA
      (fun i => if i = b then .gpu else .cta)).mutualScope b c = false := by decide

theorem different_grids_not_same_cta :
    Scope.cta.includes (differentGrid 0) (differentGrid 1) = false := by decide
theorem different_grids_same_gpu :
    Scope.gpu.includes (differentGrid 0) (differentGrid 1) = true := by decide
theorem same_cluster_different_cta :
    Scope.cluster.includes (separateCTA 0) (separateCTA 1) = true ∧
      Scope.cta.includes (separateCTA 0) (separateCTA 1) = false := by decide

def sharedAllocation : Allocation := ⟨.shared,16,4,.cta (sameCTA 0),true,true,true⟩
def sharedEnvironment : Environment := ⟨fun _ => some sharedAllocation⟩

theorem shared_owner_can_access :
    sharedEnvironment.accessible (sameCTA 1) .read ⟨.shared,0,4⟩ 4 := by decide
theorem shared_other_cta_cannot_access :
    ¬sharedEnvironment.accessible (separateCTA 1) .read ⟨.shared,0,4⟩ 4 := by decide
theorem explicit_cluster_shared_access :
    sharedEnvironment.accessible (separateCTA 1) .read ⟨.shared,0,4⟩ 4 true := by decide
theorem shared_other_grid_cannot_access :
    ¬sharedEnvironment.accessible (differentGrid 1) .read ⟨.shared,0,4⟩ 4 true := by decide
theorem misalignment_rejected :
    sharedEnvironment.checkAccess (sameCTA 0) .read ⟨.shared,0,1⟩ 4 = .error .misaligned := rfl
theorem bounds_rejected :
    sharedEnvironment.checkAccess (sameCTA 0) .read ⟨.shared,0,16⟩ 4 = .error .outOfBounds := rfl
theorem cluster_target_rejected :
    memoryEligibility ⟨94,80⟩ ⟨.read,.global,some .cluster,false⟩ =
      .illegal "cluster scope/addressing require PTX 7.8 and sm_90" := rfl
theorem cluster_target_accepted :
    memoryEligibility ⟨94,90⟩ ⟨.read,.global,some .cluster,false⟩ = .supported := rfl

def localEnvironment : Environment :=
  ⟨fun _ => some ⟨.local,8,4,.thread (sameCTA 0),true,true,true⟩⟩
theorem local_other_thread_rejected :
    ¬localEnvironment.accessible (sameCTA 1) .read ⟨.local,0,0⟩ 4 := by decide

def parameterEnvironment : Environment :=
  ⟨fun _ => some ⟨.param,8,4,.grid 0 0,true,true,true⟩⟩
theorem entry_parameter_store_rejected :
    ¬parameterEnvironment.accessible (sameCTA 0) .write ⟨.param,0,0⟩ 4 := by decide
theorem parameter_abi_explicitly_unsupported :
    memoryEligibility ⟨94,90⟩ ⟨.write,.param,none,false⟩ =
      .unsupported "device-function parameter ABI and st.param are not modeled" := rfl

/-- Out-of-scope writes need not have the legacy fragment's total coherence. -/
def racyProgram : Program := ⟨[0], [[.store .relaxed 0 1],[.store .relaxed 0 2]]⟩
def racyCo (a b : Fin 3) : Bool := a == 0 && b != 0
def racy : ScopedGraph 3 :=
  racyProgram.scopedGraph (fun _ _ => 0) (fun _ _ => 0) (fun _ : Fin 3 => (0 : Fin 3)) racyCo
    separateCTA (fun _ => .cta)
theorem racy_writes_partial_coherence : racy.Valid ∧
    ¬racy.graph.coherence 1 2 ∧ ¬racy.graph.coherence 2 1 := by decide
theorem racy_program_admitted :
    racyProgram.ScopedAdmitted (fun _ _ => 0) (fun _ _ => 0) (fun _ : Fin 3 => (0 : Fin 3)) racyCo
      separateCTA (fun _ => .cta) := by
  refine ⟨?_,?_,racy_writes_partial_coherence.1⟩
  · simp [Program.Bounded,racyProgram,Instr.address]
  · intro i _ j _ h; exact congrArg ThreadLocation.cta h
theorem racy_not_legacy_valid : ¬racy.graph.Valid := by
  intro h
  rcases h.co.total 1 2 (by trivial) (by trivial) rfl (by decide) with hc | hc
  · exact racy_writes_partial_coherence.2.1 hc
  · exact racy_writes_partial_coherence.2.2 hc

end Ptx.ScopedExamples

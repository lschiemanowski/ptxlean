import Ptx.Environment
import Ptx.Scalar

/-! A checked connection between scalar byte-address validity and the allocation
access contract. One initialized arena is mapped to one global allocation on its
issuing device. Exclusive use is a separate execution discipline: device access
permission does not establish exclusive ownership or concurrent refinement. -/
namespace Ptx.Scalar

/-- The memory contents are supplied by the caller, not implicitly zero-filled. -/
def arenaEnvironment (memory : List Word) (thread : ThreadLocation)
    (allocationId : Nat) : Environment where
  allocations := fun index => if index = allocationId then some {
    space := .global
    bytes := 4 * memory.length
    alignment := 4
    owner := .device thread.device
    readable := true
    writable := true
    initialized := true
  } else none

def arenaAddress (allocationId : Nat) (pointer : Address) : Ptx.Address :=
  ⟨.global, allocationId, pointer.toNat⟩

/-- The full byte-extent check agrees with the scalar aligned word-index check. -/
theorem arena_access_iff (memory : List Word) (thread : ThreadLocation)
    (allocationId : Nat) (pointer : Address) (kind : AccessKind) :
    (arenaEnvironment memory thread allocationId).accessible thread kind
      (arenaAddress allocationId pointer) 4 ↔ ValidAddress memory pointer := by
  have division := Nat.mod_add_div pointer.toNat 4
  cases kind <;>
    simp [Environment.accessible, Environment.checkAccess, arenaEnvironment,
      arenaAddress, Allocation.ownerAllows, ValidAddress] <;>
    (repeat' split) <;> simp_all <;> omega

/-- Every emitted access in an arbitrary local run passes the explicit allocation
contract, even if execution subsequently faults or exhausts its budget. -/
theorem run_environment_safe (fuel : Nat) (program : List Instr) (s : State)
    (thread : ThreadLocation) (allocationId : Nat)
    (event : Occurrence) (member : event ∈ (run fuel program s).trace)
    (effect : MemoryEffect) (memory : event.memory = some effect) :
    (arenaEnvironment s.memory thread allocationId).accessible thread
      (match effect.kind with | .load => .read | .store => .write)
      (arenaAddress allocationId effect.address) 4 := by
  exact (arena_access_iff ..).mpr (run_trace_safe _ _ _ event member effect memory)

/-- Distinct allocation identifiers cannot accidentally alias in this resolved
address representation. Physical address resolution still needs its own contract. -/
theorem separate_arenas (left right : Nat) (different : left ≠ right)
    (a b : Address) : arenaAddress left a ≠ arenaAddress right b := by
  intro equality
  exact different (congrArg Ptx.Address.allocation equality)

/-- The explicit relaxed GPU-scoped global forms used by the text boundary are
eligible on this concrete PTX 9.4/sm_90 target. No code-generation claim is made. -/
theorem arena_forms_eligible :
    memoryEligibility ⟨94, 90⟩ ⟨.read, .global, some .gpu, false⟩ = .supported ∧
    memoryEligibility ⟨94, 90⟩ ⟨.write, .global, some .gpu, false⟩ = .supported := by decide

end Ptx.Scalar

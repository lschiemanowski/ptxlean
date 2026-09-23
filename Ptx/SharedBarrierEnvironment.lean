import Ptx.SharedBarrierMachine
import Ptx.Environment

/-! Embed the actual shared arena in the general allocation checker.
No external launch, cluster peer, allocation lifecycle or visibility is inferred.
-/
namespace Ptx.SharedBarrier

def location (cta thread : Nat) : ThreadLocation := ⟨0, 0, 0, cta, thread⟩

def Arena.environment (arena : Arena n) : Environment where
  allocations := fun id => if id = 0 then
    some ⟨.shared, 4*n, 4, .cta (location arena.owner 0), true, true, true⟩ else none

def sharedAddress (address : Word) : Ptx.Address := ⟨.shared, 0, address.toNat⟩

def MemoryKind.accessKind : MemoryKind → AccessKind
  | .load => .read
  | .store => .write

theorem accessSafe_bytes (address : Word) (safe : AccessSafe n address) :
    address.toNat + 4 ≤ 4*n ∧ address.toNat % 4 = 0 := by
  obtain ⟨aligned, bound⟩ := safe
  exact ⟨by omega, aligned⟩

theorem arena_accessible (arena : Arena n) (cta thread : Nat) (kind : AccessKind)
    (address : Word) (owner : arena.owner = cta) (safe : AccessSafe n address) :
    arena.environment.accessible (location cta thread) kind (sharedAddress address) 4 false := by
  obtain ⟨bound, aligned⟩ := accessSafe_bytes address safe
  cases kind <;>
    simp [Environment.accessible, Environment.checkAccess, Arena.environment,
      sharedAddress, Allocation.ownerAllows, location, ThreadLocation.sameCTA,
      ThreadLocation.sameCluster, owner, aligned, Nat.not_lt.mpr bound]

/-- The ordinary checker accepts every actually emitted access, with its actual
kind and byte address. This does not require successful program completion. -/
theorem emitted_accessible (config : Config n) (override : Option Word) (thread : Fin n)
    (state : State n) (effect : MemoryEvent n)
    (member : Event.memory effect ∈ (stepWith config override thread state).events) :
    state.arena.environment.accessible (location effect.cta effect.thread.val)
      effect.kind.accessKind (sharedAddress effect.address) 4 false := by
  obtain ⟨owner, safe, cta, _, _⟩ := memory_safe config override thread state effect member
  apply arena_accessible
  · exact owner.trans cta.symm
  · exact safe

end Ptx.SharedBarrier

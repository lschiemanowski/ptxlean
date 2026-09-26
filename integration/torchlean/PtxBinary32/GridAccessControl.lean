import PtxBinary32.GridInvariants
import PtxBinary32.ParallelLoadControl
import PtxBinary32.ParallelStoreControl

/-! Actual grid memory events retain their fetched instruction, guard and
projected address. Tensor values never become an address premise. -/
namespace Ptx.Scalar.Parallel.Grid

theorem step_memory_origin {s final : State groups n} {events : List (Event groups n)}
    (step : Step cfg program s events final) (g : Fin groups) (t : Fin n) (space : Space)
    (occ : Scalar.Occurrence) (effect : MemoryEffect)
    (member : (g,.scalar t (some space) occ) ∈ events) (memory : occ.memory=some effect) :
    program[occ.pc]?=some (.memory space occ.instruction) ∧ occ.executed=true ∧
      Memory.Prior.memoryKind occ.instruction.op=some effect.kind := by
  cases step with
  | issue selected thread candidate out step =>
    change (g,.scalar t (some space) occ) ∈ out.events.map (fun e => (selected,e)) at member
    obtain ⟨event,inside,eq⟩ := List.mem_map.mp member
    obtain ⟨rfl,rfl⟩ := Prod.mk.inj eq
    have complete := Memory.run_access_complete (Parallel.Runs.cons step Parallel.Runs.nil) (by simpa using inside) memory
    simpa [Memory.access,memory] using complete

theorem run_memory_origin {s final : State groups n} {events : List (Event groups n)}
    (run : Runs cfg program s events final) (g : Fin groups) (t : Fin n) (space : Space)
    (occ : Scalar.Occurrence) (effect : MemoryEffect)
    (member : (g,.scalar t (some space) occ) ∈ events) (memory : occ.memory=some effect) :
    program[occ.pc]?=some (.memory space occ.instruction) ∧ occ.executed=true ∧
      Memory.Prior.memoryKind occ.instruction.op=some effect.kind := by
  induction run with
  | nil => simp at member
  | cons step _ ih =>
    rcases List.mem_append.mp member with now | later
    · exact step_memory_origin step g t space occ effect now memory
    · exact ih later

theorem run_store {s final : State groups n} {events : List (Event groups n)}
    (run : Runs cfg program s events final) (seeds : Fin groups → Fin n → Scalar.State)
    (compatible : AddressControl.ProgramCompatible program)
    (aligned : ∀ g, Parallel.Aligned (view s g))
    (initial : ∀ g, AddressControl.Invariant program (seeds g) (view s g))
    (g : Fin groups) (owner : Fin n) (space : Option Space) (occ : Scalar.Occurrence) (effect : MemoryEffect)
    (member : (g,.scalar owner space occ) ∈ events) (memory : occ.memory=some effect) (store : effect.kind=.store) :
    ∃ address value, occ.instruction.op=.store address value ∧
      effect.address=address.eval (AddressControl.atPC program (seeds g owner) occ.pc) ∧
      (occ.instruction.guard=.pred 0 true → (AddressControl.atPC program (seeds g owner) occ.pc).preds 0=true) := by
  induction run with
  | nil => simp at member
  | cons step _ ih =>
    rcases List.mem_append.mp member with now | later
    · cases step with
      | issue selected thread candidate out step =>
        change (g,.scalar owner space occ) ∈ out.events.map (fun e => (selected,e)) at now
        obtain ⟨event,inside,eq⟩ := List.mem_map.mp now
        obtain ⟨rfl,rfl⟩ := Prod.mk.inj eq
        exact AddressControl.step_store step (initial selected) inside memory store
    · exact ih (step_aligned step aligned)
        (runs_address_control (Runs.cons step Runs.nil) seeds compatible aligned initial) later

theorem run_load {s final : State groups n} {events : List (Event groups n)}
    (run : Runs cfg program s events final) (seeds : Fin groups → Fin n → Scalar.State)
    (compatible : AddressControl.ProgramCompatible program)
    (aligned : ∀ g, Parallel.Aligned (view s g))
    (initial : ∀ g, AddressControl.Invariant program (seeds g) (view s g))
    (g : Fin groups) (owner : Fin n) (space : Option Space) (occ : Scalar.Occurrence) (effect : MemoryEffect)
    (member : (g,.scalar owner space occ) ∈ events) (memory : occ.memory=some effect) (load : effect.kind=.load) :
    ∃ destination address, occ.instruction.op=.load destination address ∧
      effect.address=address.eval (AddressControl.atPC program (seeds g owner) occ.pc) ∧
      (occ.instruction.guard=.pred 0 true → (AddressControl.atPC program (seeds g owner) occ.pc).preds 0=true) := by
  induction run with
  | nil => simp at member
  | cons step _ ih =>
    rcases List.mem_append.mp member with now | later
    · cases step with
      | issue selected thread candidate out step =>
        change (g,.scalar owner space occ) ∈ out.events.map (fun e => (selected,e)) at now
        obtain ⟨event,inside,eq⟩ := List.mem_map.mp now
        obtain ⟨rfl,rfl⟩ := Prod.mk.inj eq
        exact AddressControl.step_load step (initial selected) inside memory load
    · exact ih (step_aligned step aligned)
        (runs_address_control (Runs.cons step Runs.nil) seeds compatible aligned initial) later

end Ptx.Scalar.Parallel.Grid

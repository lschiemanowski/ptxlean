import PtxBinary32.Sequential
import PtxBinary32.Affine
import PtxBinary32.SquareError
import PtxAffineSquareVJP

/-! Actual serialized kernels for a scalar squared-affine graph. Each launch
executes the existing seven-instruction affine program with independent supplied
registers. Runtime completion/visibility is the separate serialized contract. -/
namespace PtxTorchLean.AffineSquareKernel
open Ptx Ptx.Scalar Ptx.Scalar.Sequential Ptx.SequentialStorage

/-- The last word is an explicit positive-zero input before it becomes output. -/
def memory (x w b old : Word) (tail : List Word) : List Word := [x,w,b,old,0] ++ tail

def outputMemory (x w b intermediate output : Word) (tail : List Word) : List Word :=
  [x,w,b,intermediate,output] ++ tail

def firstArgs (allocation : Nat) (i : Fin 4) : Argument :=
  ⟨allocation, match i.val with | 0 => 0 | 1 => 4 | 2 => 8 | _ => 12⟩

def secondArgs (allocation : Nat) (i : Fin 4) : Argument :=
  ⟨allocation, if i.val < 2 then 12 else 16⟩

def firstStart (seed : Seed) (allocation : Nat) (x w b old : Word) (tail : List Word) : State :=
  start seed (firstArgs allocation) (memory x w b old tail)

def secondStart (seed : Seed) (allocation : Nat) (x w b intermediate : Word) (tail : List Word) : State :=
  start seed (secondArgs allocation) (memory x w b intermediate tail)

def request (target : Target) (thread : ThreadLocation) (allocation : Nat)
    (seed : Seed) (args : Fin 4 → Argument) : Request :=
  ⟨target, Affine.program, thread, allocation, 4, args, seed⟩

def firstRequest (target : Target) (thread : ThreadLocation) (allocation : Nat) (seed : Seed) : Request :=
  request target thread allocation seed (firstArgs allocation)

def secondRequest (target : Target) (thread : ThreadLocation) (allocation : Nat) (seed : Seed) : Request :=
  request target thread allocation seed (secondArgs allocation)

variable {seed : Seed} {allocation : Nat} {x w b old intermediate product square output : Word}
  {tail : List Word} {target : Target} {final : State} {events : List Mixed.Event}

theorem first_initial : Affine.Initial (firstStart seed allocation x w b old tail) := by
  constructor
  · rfl
  · intro i; fin_cases i <;>
      simp [firstStart, start, firstArgs, memory, ValidAddress]

theorem second_initial : Affine.Initial (secondStart seed allocation x w b intermediate tail) := by
  constructor
  · rfl
  · intro i; fin_cases i <;>
      simp [secondStart, start, secondArgs, memory, ValidAddress]

theorem first_run_iff (eligible : Mixed.Eligible target) :
    Mixed.Run target Affine.program (firstStart seed allocation x w b old tail) final .halted events ↔
      ∃ product intermediate, Binary32.Error.AffineResults x w b product intermediate ∧
        final = Affine.finish (firstStart seed allocation x w b old tail) product intermediate ∧
        events = Affine.trace (firstStart seed allocation x w b old tail) product intermediate := by
  simpa [Affine.input, firstStart, start, firstArgs, memory] using
    Affine.run_iff (firstStart seed allocation x w b old tail) target first_initial eligible final .halted events

theorem second_run_iff (eligible : Mixed.Eligible target) :
    Mixed.Run target Affine.program (secondStart seed allocation x w b intermediate tail) final .halted events ↔
      ∃ square output, Binary32.Error.AffineResults intermediate intermediate 0 square output ∧
        final = Affine.finish (secondStart seed allocation x w b intermediate tail) square output ∧
        events = Affine.trace (secondStart seed allocation x w b intermediate tail) square output := by
  simpa [Affine.input, secondStart, start, secondArgs, memory] using
    Affine.run_iff (secondStart seed allocation x w b intermediate tail) target second_initial eligible final .halted events

theorem first_memory :
    (Affine.finish (firstStart seed allocation x w b old tail) product intermediate).memory =
      memory x w b intermediate tail := by
  simp [Affine.finish, Affine.afterAdd, Affine.afterMultiply, Affine.afterBias,
    Affine.afterRight, Affine.afterLeft, Affine.outputIndex, firstStart, start, firstArgs, memory]

theorem second_memory :
    (Affine.finish (secondStart seed allocation x w b intermediate tail) square output).memory =
      outputMemory x w b intermediate output tail := by
  simp [Affine.finish, Affine.afterAdd, Affine.afterMultiply, Affine.afterBias,
    Affine.afterRight, Affine.afterLeft, Affine.outputIndex, secondStart, start, secondArgs, memory, outputMemory]

variable {before middle after : Store} {thread : ThreadLocation} {firstSeed secondSeed : Seed}
  {firstFinal secondFinal : State} {firstTrace secondTrace : List Mixed.Event}

/-- Every pair of completed launches uses the stored intermediate twice in the
second launch. Neither the arithmetic result nor the memory handoff is a premise. -/
theorem launches_correct
    (present : before.cells allocation = some ⟨thread.device, memory x w b old tail⟩)
    (eligible : Mixed.Eligible target)
    (first : SuccessfulLaunch (firstRequest target thread allocation firstSeed)
      before middle firstFinal firstTrace)
    (second : SuccessfulLaunch (secondRequest target thread allocation secondSeed)
      middle after secondFinal secondTrace) :
    ∃ product intermediate square output,
      Binary32.SquareError.Results x w b product intermediate square output ∧
      middle.cells allocation = some ⟨thread.device, memory x w b intermediate tail⟩ ∧
      after.cells allocation = some ⟨thread.device, outputMemory x w b intermediate output tail⟩ ∧
      firstFinal = Affine.finish (firstStart firstSeed allocation x w b old tail) product intermediate ∧
      firstTrace = Affine.trace (firstStart firstSeed allocation x w b old tail) product intermediate ∧
      secondFinal = Affine.finish (secondStart secondSeed allocation x w b intermediate tail) square output ∧
      secondTrace = Affine.trace (secondStart secondSeed allocation x w b intermediate tail) square output := by
  have run₁ := first.run_from present
  obtain ⟨product, intermediate, result₁, state₁, trace₁⟩ := (first_run_iff eligible).mp run₁
  have saved := first.writeback_lookup present
  have middleCell : middle.cells allocation = some ⟨thread.device, memory x w b intermediate tail⟩ := by
    simpa only [firstRequest, request, state₁, first_memory] using saved
  have run₂ := second.run_from middleCell
  obtain ⟨square, output, result₂, state₂, trace₂⟩ := (second_run_iff eligible).mp run₂
  have saved₂ := second.writeback_lookup middleCell
  have afterCell : after.cells allocation = some ⟨thread.device, outputMemory x w b intermediate output tail⟩ := by
    simpa only [secondRequest, request, state₂, second_memory] using saved₂
  exact ⟨product, intermediate, square, output, ⟨result₁, result₂⟩, middleCell, afterCell,
    state₁, trace₁, state₂, trace₂⟩

/-- Construct the actual runs and writebacks from four permitted instruction
results. The public existence theorem below supplies these results for all bits. -/
theorem pipeline_of_results
    (present : before.cells allocation = some ⟨thread.device, memory x w b old tail⟩)
    (eligible : Mixed.Eligible target)
    (allowed : Binary32.SquareError.Results x w b product intermediate square output) :
    ∃ after, Chain before [firstRequest target thread allocation firstSeed,
      secondRequest target thread allocation secondSeed] after ∧
      after.cells allocation = some ⟨thread.device, outputMemory x w b intermediate output tail⟩ := by
  have run₁ := (first_run_iff (seed := firstSeed) (allocation := allocation)
    (x := x) (w := w) (b := b) (old := old) (tail := tail)
    (final := Affine.finish (firstStart firstSeed allocation x w b old tail) product intermediate)
    (events := Affine.trace (firstStart firstSeed allocation x w b old tail) product intermediate)
    eligible).mpr ⟨product, intermediate, allowed.1, rfl, rfl⟩
  obtain ⟨middle, first⟩ := launch_exists
    (request := firstRequest target thread allocation firstSeed) present rfl (fun _ => rfl) run₁
  have middleCell : middle.cells allocation = some ⟨thread.device, memory x w b intermediate tail⟩ := by
    simpa only [firstRequest, request, first_memory] using first.writeback_lookup present
  have run₂ := (second_run_iff (seed := secondSeed) (allocation := allocation)
    (x := x) (w := w) (b := b) (intermediate := intermediate) (tail := tail)
    (final := Affine.finish (secondStart secondSeed allocation x w b intermediate tail) square output)
    (events := Affine.trace (secondStart secondSeed allocation x w b intermediate tail) square output)
    eligible).mpr ⟨square, output, allowed.2, rfl, rfl⟩
  obtain ⟨after, second⟩ := launch_exists
    (request := secondRequest target thread allocation secondSeed) middleCell rfl (fun _ => rfl) run₂
  refine ⟨after, .cons first (.cons second .nil), ?_⟩
  simpa only [secondRequest, request, second_memory] using second.writeback_lookup middleCell

/-- Terminating two-kernel execution exists for every initial bit pattern and
independently supplied register state; no finite-value or output premise. -/
theorem pipeline_exists
    (present : before.cells allocation = some ⟨thread.device, memory x w b old tail⟩)
    (eligible : Mixed.Eligible target) :
    ∃ after, Chain before [firstRequest target thread allocation firstSeed,
      secondRequest target thread allocation secondSeed] after := by
  obtain ⟨product, intermediate, square, output, allowed⟩ := Binary32.SquareError.results_exists x w b
  obtain ⟨after, chain, _⟩ := pipeline_of_results (firstSeed := firstSeed) (secondSeed := secondSeed)
    present eligible allowed
  exact ⟨after, chain⟩

/-- Universal correspondence for every admitted completed pipeline. -/
theorem pipeline_correct
    (present : before.cells allocation = some ⟨thread.device, memory x w b old tail⟩)
    (eligible : Mixed.Eligible target)
    (chain : Chain before [firstRequest target thread allocation firstSeed,
      secondRequest target thread allocation secondSeed] after) :
    ∃ product intermediate square output,
      Binary32.SquareError.Results x w b product intermediate square output ∧
      after.cells allocation = some ⟨thread.device, outputMemory x w b intermediate output tail⟩ := by
  obtain ⟨middle, final₁, trace₁, final₂, trace₂, first, second⟩ := Chain.two_iff.mp chain
  obtain ⟨product, intermediate, square, output, results, _, saved, _⟩ :=
    launches_correct present eligible first second
  exact ⟨product, intermediate, square, output, results, saved⟩

/-- Other logical allocations are preserved by both launches. -/
theorem pipeline_frame
    (chain : Chain before [firstRequest target thread allocation firstSeed,
      secondRequest target thread allocation secondSeed] after)
    (other : Nat) (different : other ≠ allocation) : after.cells other = before.cells other := by
  obtain ⟨middle, final₁, trace₁, final₂, trace₂, first, second⟩ := Chain.two_iff.mp chain
  exact (second.other_cell different).trans (first.other_cell different)

/-- The actual stored output approximates the real-valued upstream TorchLean
forward graph. Every numerical range guard concerns the initial encoded inputs. -/
theorem stored_forward_error
    (present : before.cells allocation = some ⟨thread.device, memory x w b old tail⟩)
    (eligible : Mixed.Eligible target)
    (chain : Chain before [firstRequest target thread allocation firstSeed,
      secondRequest target thread allocation secondSeed] after)
    (xh wh bh idealX idealW idealB ex ew eb : ℝ)
    (leftReal : Binary32.finiteReal x = some xh)
    (weightReal : Binary32.finiteReal w = some wh)
    (biasReal : Binary32.finiteReal b = some bh)
    (multiplyRange : |xh*wh| ≤ Binary32.Bounds.maxFinite)
    (additionRange : |xh*wh| + TorchLean.Floats.eps32 (xh*wh) + |bh| ≤ Binary32.Bounds.maxFinite)
    (squareRange : |Binary32.SquareError.roundedAffine xh wh bh *
      Binary32.SquareError.roundedAffine xh wh bh| ≤ Binary32.Bounds.maxFinite)
    (finalRange : |Binary32.SquareError.roundedAffine xh wh bh *
      Binary32.SquareError.roundedAffine xh wh bh| +
      TorchLean.Floats.eps32 (Binary32.SquareError.roundedAffine xh wh bh *
        Binary32.SquareError.roundedAffine xh wh bh) ≤ Binary32.Bounds.maxFinite)
    (leftError : |xh-idealX| ≤ ex) (weightError : |wh-idealW| ≤ ew) (biasError : |bh-idealB| ≤ eb) :
    ∃ intermediate output z,
      after.cells allocation = some ⟨thread.device, outputMemory x w b intermediate output tail⟩ ∧
      Binary32.finiteReal output = some z ∧
      |z-TorchLean.Tensor.item (AffineSquareVJP.graph.forward
        (AffineSquareVJP.inputs idealX idealW idealB))| ≤
        Binary32.SquareError.budget xh wh bh idealX idealW idealB ex ew eb := by
  obtain ⟨product, intermediate, square, output, allowed, saved⟩ :=
    pipeline_correct present eligible chain
  obtain ⟨_, _, z, real, error⟩ := Binary32.SquareError.results_error
    x w b product intermediate square output xh wh bh idealX idealW idealB ex ew eb
    leftReal weightReal biasReal multiplyRange additionRange squareRange finalRange
    leftError weightError biasError allowed
  exact ⟨intermediate, output, z, saved, real, by rw [AffineSquareVJP.forward_value]; exact error⟩

/-- A real instruction execution example: first 1.5*2+0.25 = 3.25, then
3.25*3.25+0 = 10.5625. Both incoming register banks are arbitrary. -/
theorem two_launch_example (firstSeed secondSeed : Seed) :
    ∃ after, Chain
      (reserve empty 0 (memory 0x3fc00000 0x40000000 0x3e800000 0xdeadbeef [])).2
      [firstRequest ⟨94,70⟩ ⟨0,0,0,0,0⟩ 0 firstSeed,
       secondRequest ⟨94,70⟩ ⟨0,0,0,0,0⟩ 0 secondSeed] after ∧
      after.cells 0 = some ⟨0, [0x3fc00000,0x40000000,0x3e800000,0x40500000,0x41290000]⟩ := by
  apply pipeline_of_results (product := 0x40400000) (square := 0x41290000)
    (old := 0xdeadbeef) (by rfl) (by constructor <;> decide)
  constructor
  · constructor
    · change Binary32.Envelope (Binary32.reference .mul 0x3fc00000 0x40000000) 0x40400000
      exact Binary32.envelope_self _
    · change Binary32.Envelope (Binary32.reference .add 0x40400000 0x3e800000) 0x40500000
      exact Binary32.envelope_self _
  · constructor
    · change Binary32.Envelope (Binary32.reference .mul 0x40500000 0x40500000) 0x41290000
      exact Binary32.envelope_self _
    · change Binary32.Envelope (Binary32.reference .add 0x41290000 0) 0x41290000
      exact Binary32.envelope_self _

/-- Replacing the intermediate allocation cannot revive the second launch's old
handle, even after arbitrarily many intervening storage operations. -/
theorem second_launch_after_release_rejected
    (released : release middle allocation = some freed) (history : History freed last) :
    ¬ SuccessfulLaunch (secondRequest target thread allocation secondSeed) last after final events :=
  no_launch_after_release released history

end PtxTorchLean.AffineSquareKernel

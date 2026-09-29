import PoissonPTX.CellFinalTensor

/-! Phase-by-phase composition using bytes reconstructed from actual middle-run
stores. This is not a theorem about final loads in one concurrent full-cell run. -/
namespace PtxTorchLean.Poisson.PTX.CellFinal
open Concurrent
open Concurrent.CellMiddle
open Correspondence

/-- Little-endian materialization of aligned word storage. -/
def wordBytes (memory : Nat → Word) : Memory :=
  fun address => byte (memory (address/8*8)) (address%8)

theorem read_wordBytes (memory : Nat → Word) (address : Nat) (aligned : address%8=0) :
    read64 (wordBytes memory) address=memory address := by
  apply Sources.word_eq_of_bytes
  intro k
  rw [Sources.byte_read64]
  have bound := k.isLt
  have div : (address+k.val)/8=address/8 := by omega
  have mod : (address+k.val)%8=k.val := by omega
  simp only [wordBytes,div,mod]
  rw [show address/8*8=address by omega]

/-- The shared input is constructed from the middle run's real store records;
the global coefficient bytes retain their initial values. -/
def phaseState (entry : PTX.State) (width : Nat) (baseWords : Space → Word)
    (initial : Space → Memory) (events : List (Event 32)) : PTX.State :=
  {entry with
    global := initial .global
    shared :=wordBytes (Numeric.view width baseWords initial events .shared)}

theorem phase_global (entry : PTX.State) (base : entry.regs 0=baseWords .global) (offset : Nat) :
    grid (phaseState entry width baseWords initial events) width .global offset=
      Numeric.grid width baseWords (Numeric.view width baseWords initial events) .global offset := by
  funext i j
  simp [grid,Numeric.grid,words,CellFinal.bases,Contraction.baseRegister,phaseState,State.memory,base,
    Numeric.view,CellMiddle.WordView.memory]

theorem phase_shared (entry : PTX.State) (base : entry.regs 3=baseWords .shared)
    (launch : Numeric.Launch width baseWords start) (aligned : (baseWords .shared).toNat%8=0)
    (plane : Fin 7) :
    grid (phaseState entry width baseWords initial events) width .shared (plane.val*width*width*8)=
      Numeric.grid width baseWords (Numeric.view width baseWords initial events) .shared (plane.val*width*width*8) := by
  funext i j
  simp only [grid,Numeric.grid,words,CellFinal.bases,Contraction.baseRegister,phaseState,State.memory,base]
  rw [Numeric.shared_word_address launch plane i j]
  rw [read_wordBytes _ _ (by simp [SharedPlane.address,Nat.add_mod,aligned])]

/-- The actual middle-run tensors determine the final body's byte-backed
calculation. No equality asserting a producer's expected answer is an input. -/
theorem phase_result (entry : PTX.State) (lo : 2≤width) (hi : width≤5)
    (launch : Numeric.Launch width baseWords start)
    (aligned : (baseWords .shared).toNat%8=0)
    (global : entry.regs 0=baseWords .global) (shared : entry.regs 3=baseWords .shared)
    (i j : Fin width) (row : (entry.regs 16).toNat=i.val) (col : (entry.regs 17).toNat=j.val)
    (execution : Concurrent.Runs cfg (CellMiddle.Checks.program width) start events final)
    (done : ∀ t, (final.lanes t).pc=(CellMiddle.Checks.program width).length)
    (compatible : Visibility.Compatible initial events source) (performed : Visibility.Performed events source) :
    result (phaseState entry width baseWords initial events) width 0 (CellMiddle.Checks.derivativeOffset width)=
      Spec.get2 (localAction
        (Numeric.initialTensor width baseWords initial .global 0)
        (Numeric.initialTensor width baseWords initial .global (width*width*8+32))
        (Numeric.initialTensor width baseWords initial .global (2*(width*width*8+32)))
        (Numeric.initialTensor width baseWords initial .shared 0)) i j := by
  have formula := result_tensor (phaseState entry width baseWords initial events) hi 0 (width*width*8+32) i j row col
  have p5 := phase_shared (initial:=initial) (events:=events) entry shared launch aligned ⟨5,by decide⟩
  have p6 := phase_shared (initial:=initial) (events:=events) entry shared launch aligned ⟨6,by decide⟩
  have m5 := Numeric.completed_middle launch lo hi execution done compatible performed ⟨5,by decide⟩ (by decide)
  have m6 := Numeric.completed_middle launch lo hi execution done compatible performed ⟨6,by decide⟩ (by decide)
  rw [m5] at p5
  rw [m6] at p6
  have g (offset : Nat) := (phase_global (width:=width) (initial:=initial) (events:=events) entry global offset).trans
    (Numeric.global_grid width baseWords initial events offset)
  change _=entries _ i j at formula ⊢
  simp only [entries_summed,entries_product,entries_matrix] at formula
  rw [p5,p6,g,g] at formula
  simpa [CellMiddle.Checks.derivativeOffset,Numeric.target,localAction,entries_summed,entries_product] using formula

/-- Phase-by-phase correspondence: actual middle stores construct the shared
bytes; a fetched final-body run produces the TorchLean local cell result. The
single concurrent trace through final reads remains a separate obligation. -/
theorem completed_from_middle (entry : PTX.State) (lo : 2≤width) (hi : width≤5)
    (launch : Numeric.Launch width baseWords start) (aligned : (baseWords .shared).toNat%8=0)
    (global : entry.regs 0=baseWords .global) (shared : entry.regs 3=baseWords .shared)
    (i j : Fin width) (row : (entry.regs 16).toNat=i.val) (col : (entry.regs 17).toNat=j.val)
    (execution : Concurrent.Runs cfg (CellMiddle.Checks.program width) start events middle)
    (done : ∀ t, (middle.lanes t).pc=(CellMiddle.Checks.program width).length)
    (compatible : Visibility.Compatible initial events source) (performed : Visibility.Performed events source)
    (inputs : Inputs (phaseState entry width baseWords initial events) width 0 (CellMiddle.Checks.derivativeOffset width))
    (valid : Valid64 entry.globalStart entry.globalBytes (location entry width output).toNat)
    (precode : List Kernel.Instr) (pc : entry.pc=precode.length)
    (finalRun : Kernel.Run ctx (precode++program width 0 (CellMiddle.Checks.derivativeOffset width) output)
      ⟨phaseState entry width baseWords initial events,false,false⟩ endState) :
    decode (read64 endState.core.global (location entry width output).toNat)=
      Spec.get2 (localAction
        (Numeric.initialTensor width baseWords initial .global 0)
        (Numeric.initialTensor width baseWords initial .global (width*width*8+32))
        (Numeric.initialTensor width baseWords initial .global (2*(width*width*8+32)))
        (Numeric.initialTensor width baseWords initial .shared 0)) i j := by
  have h := (fetched_correct rfl inputs valid precode pc finalRun).1
  exact h.trans (phase_result entry lo hi launch aligned global shared i j row col execution done compatible performed)

/-- Existence is independent of the final-run hypothesis of correspondence:
valid final storage supplies a fetched completion with the local cell result. -/
theorem exists_from_middle (entry : PTX.State) (lo : 2≤width) (hi : width≤5)
    (launch : Numeric.Launch width baseWords start) (aligned : (baseWords .shared).toNat%8=0)
    (global : entry.regs 0=baseWords .global) (shared : entry.regs 3=baseWords .shared)
    (i j : Fin width) (row : (entry.regs 16).toNat=i.val) (col : (entry.regs 17).toNat=j.val)
    (execution : Concurrent.Runs cfg (CellMiddle.Checks.program width) start events middle)
    (done : ∀ t, (middle.lanes t).pc=(CellMiddle.Checks.program width).length)
    (compatible : Visibility.Compatible initial events source) (performed : Visibility.Performed events source)
    (inputs : Inputs (phaseState entry width baseWords initial events) width 0 (CellMiddle.Checks.derivativeOffset width))
    (valid : Valid64 entry.globalStart entry.globalBytes (location entry width output).toNat)
    (precode : List Kernel.Instr) (pc : entry.pc=precode.length)
 :
    ∃ endState, Kernel.Run ctx (precode++program width 0 (CellMiddle.Checks.derivativeOffset width) output)
      ⟨phaseState entry width baseWords initial events,false,false⟩ endState ∧
    decode (read64 endState.core.global (location entry width output).toNat)=
      Spec.get2 (localAction
        (Numeric.initialTensor width baseWords initial .global 0)
        (Numeric.initialTensor width baseWords initial .global (width*width*8+32))
        (Numeric.initialTensor width baseWords initial .global (2*(width*width*8+32)))
        (Numeric.initialTensor width baseWords initial .shared 0)) i j := by
  obtain ⟨endState,run⟩ := fetched_exists (ctx:=ctx)
    (⟨phaseState entry width baseWords initial events,false,false⟩ : Kernel.State)
    rfl inputs valid precode pc
  exact ⟨endState,run,completed_from_middle entry lo hi launch aligned global shared i j row col
    execution done compatible performed inputs valid precode pc run⟩

end PtxTorchLean.Poisson.PTX.CellFinal

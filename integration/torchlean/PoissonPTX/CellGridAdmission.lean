import PoissonPTX.CellGridIndices
import PoissonPTX.CellCandidateBounds
import PoissonPTX.CellFamily

namespace PtxTorchLean.Poisson.PTX.CellGrid

/-- Actual candidate executions sharing uploaded global memory and a contiguous
cell output array. Source admission is deliberately absent at this stage. -/
structure Candidates (o : Operator) (values : Array Float) where
  (base output : Word)
  memory : Memory
  small : o.mesh.cells.size≤2^32
  candidate : ∀ i : Fin o.mesh.cells.size, CellWhole.Candidate o values (BitVec.ofNat 32 i.val)
  sameInitial : ∀ i, (candidate i).memory .global=memory
  sameCTA : ∀ i, (candidate i).cfg.cta=i.val
  sameBase : ∀ i, (candidate i).bases .global=base
  sameOutput : ∀ i, (candidate i).output=output

variable {o : Operator} {values : Array Float}

theorem Candidates.store_lower (c : Candidates o values) (block : Fin o.mesh.cells.size)
    (member : Concurrent.Event.data owner access∈(c.candidate block).events)
    (store : access.data.store=true) (global : access.space=.global) :
    c.base.toNat+c.output.toNat≤access.data.address := by
  have address := ((c.candidate block).global_store member store global).2
  rw [c.sameBase,c.sameOutput] at address
  omega

/-- All connectivity reads are fixed by actual global source admission and the
source-independent store fence, including writes from other blocks. -/
theorem Candidates.index_values (c : Candidates o values)
    (events : List (Event o.mesh.cells.size)) (indices : List (Index o.mesh.cells.size))
    (projected : ∀ block, forBlock block events=(c.candidate block).events)
    (indexProjected : ∀ block, forBlock block indices=(c.candidate block).indices)
    (compatible : IndexCompatible c.memory events indices source) (block : Fin o.mesh.cells.size) :
    CellEntry.Indices c.memory (c.candidate block).indices := by
  intro owner access member
  have upper := (c.candidate block).index_bound member
  rw [c.sameBase,c.sameOutput] at upper
  rw [← indexProjected] at member
  obtain ⟨r,observed⟩ := List.mem_iff_getElem?.mp member
  apply index_initial compatible observed upper
  intro other writer wa found store global
  rw [projected] at found
  exact c.store_lower other found store global

/-- All actual global reads precede the output region, while shared storage is
private to a block. Thus foreign stores cannot supply any read byte. -/
theorem Candidates.separated (c : Candidates o values)
    (events : List (Event o.mesh.cells.size))
    (projected : ∀ block, forBlock block events=(c.candidate block).events)
    (indexValues : ∀ block, CellEntry.Indices c.memory (c.candidate block).indices) :
    NoForeignOverlap events := by
  intro block other different reader ra writer wa observed read found store j k
  rw [projected] at observed found
  cases ws : wa.space <;> cases rs : ra.space
  · have low := c.store_lower other found store ws
    have values : CellEntry.Indices ((c.candidate block).memory .global) (c.candidate block).indices := by
      rw [c.sameInitial]; exact indexValues block
    have high := (c.candidate block).word_bound values observed read rs
    rw [c.sameBase,c.sameOutput] at high
    intro equal
    have address := ByteAddress.global.inj equal
    have bound := k.isLt
    omega
  · simp [byteAddress]
  · simp [byteAddress]
  · simpa only [ws,rs] using shared_private other block (Ne.symm different)
      (wa.data.address+j.val) (ra.data.address+k.val)

/-- Complete source admission from the one grid history. No desired read word,
cell tensor or output value appears as a premise. The grid's byte identities
and barrier rule supply the original per-cell correspondence contracts. -/
def Candidates.withSources (c : Candidates o values)
    (events : List (Event o.mesh.cells.size)) (indices : List (Index o.mesh.cells.size))
    (projected : ∀ block, forBlock block events=(c.candidate block).events)
    (indexProjected : ∀ block, forBlock block indices=(c.candidate block).indices)
    (wordSource : Sources o.mesh.cells.size) (indexSource : IndexChoices o.mesh.cells.size)
    (words : Compatible c.memory (fun block => (c.candidate block).memory .shared) events wordSource)
    (indexes : IndexCompatible c.memory events indices indexSource)
    (performed : Performed events wordSource) : CellWhole.Family o values := by
  have indexValues := c.index_values events indices projected indexProjected indexes
  have apart := c.separated events projected indexValues
  let executed (block : Fin o.mesh.cells.size) : CellWhole.Execution o values (BitVec.ofNat 32 block.val) :=
    (c.candidate block).withSources (localSource wordSource block) (fun _ _ => .initial)
      (by rw [c.sameInitial]; exact CellEntry.Control.indices_compatible (indexValues block))
      (by
        have result := compatible_project words apart block
        rw [projected] at result
        have memoryEq : (c.candidate block).memory=initial c.memory (fun block => (c.candidate block).memory .shared) block := by
          funext space
          cases space
          · exact c.sameInitial block
          · rfl
        rw [memoryEq]
        exact result)
      (by have result := performed_project performed block; simpa only [projected] using result)
  exact ⟨c.base,c.output,c.memory,c.small,executed,c.sameInitial,c.sameCTA,c.sameBase,c.sameOutput⟩

end PtxTorchLean.Poisson.PTX.CellGrid

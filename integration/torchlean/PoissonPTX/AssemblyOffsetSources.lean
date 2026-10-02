import PoissonPTX.AssemblyOffsetRecords
import PoissonPTX.AssemblyInputSeparation

namespace PtxTorchLean.Poisson.PTX.Assembly
variable {n : Nat} {a : Arena n} {memory : Memory} {regs : Fin n → Registers}
  {t : Fin n → Flow.State} {words : List (Concurrent.Event n)} {indices : List (Fin n × IndexSources.Access)}
  {thread : Fin n} {read : IndexSources.Access} {next : Bool}

/-- The actual offset-read record names the corresponding node-table slot,
including the second slot and its nonwrapping increment. -/
theorem Arena.offset_record
    (run : Flow.Parallel.Runs a.context
      (entryCode (BitVec.ofNat 32 n) a.offsets a.entries a.element mask a.boundary a.output)
      (fun i => a.start memory (regs i)) words indices t)
    (observed : (thread,read)∈indices) (which : read.pc=(if next then 14 else 9)) :
    read.address=a.base.toNat+a.offsets.toNat+(thread.val+(if next then 1 else 0))*4 := by
  have actual := ObservedAddress.offset_records (Flow.Parallel.project run thread)
    (ObservedAddress.initial rfl) (ObservedAddress.offsets_initial rfl)
    (Flow.Parallel.index_member.mpr observed) which
  have idx : (if next then Kernel.u32 (ObservedAddress.nextWord (a.context thread))
      else Kernel.Residual.index (a.context thread)).toNat=thread.val+(if next then 1 else 0) := by
    cases next
    · simpa using a.index thread
    · simpa [ObservedAddress.nextWord,ObservedAddress.nodeWord] using a.offset_index thread true
  have bound : thread.val+(if next then 1 else 0)<n+1 := by have := thread.isLt; cases next <;> simp <;> omega
  rw [actual]
  change (address32 a.base _ a.offsets).toNat=_
  rw [address32_exact _ _ _ (by rw [idx]; have := a.offsetsFit; have := a.noWrap; omega),idx]
  omega

/-- Initialization of both cursor bounds follows from the same joint source
assignment and independently established actual store ownership. -/
theorem Arena.offset_source
    (run : Flow.Parallel.Runs a.context
      (entryCode (BitVec.ofNat 32 n) a.offsets a.entries a.element mask a.boundary a.output)
      (fun i => a.start memory (regs i)) words indices t)
    (compatible : IndexSources.Compatible memory words indices indexSource)
    (separated : a.InputSeparation)
    (observed : (thread,read)∈indices) (which : read.pc=(if next then 14 else 9)) :
    read.value.toNat=a.offset memory (thread.val+(if next then 1 else 0)) := by
  have located := a.offset_record run observed which
  have value := a.index_initial run compatible observed located
    (show thread.val+(if next then 1 else 0)<n+1 by have := thread.isLt; cases next <;> simp <;> omega)
    separated.offsets
  rw [value,located]
  rfl

end PtxTorchLean.Poisson.PTX.Assembly

import PoissonPTX.ConcurrentProjection
import PoissonPTX.CellCoefficientReads
import PoissonPTX.CellFinalLayout

namespace PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.Output
open CellMiddle Correspondence

/-- Derive the output-side separation from the emitted low-word integer index
and widened byte address. Without the index and address bounds this is false. -/
theorem after_coefficients (s : PTX.State) (hi : width≤5)
    (bound : (s.regs 15).toNat*(width*width)+(s.regs 14).toNat<2^32)
    (nowrap : (s.regs 0).toNat+((s.regs 15).toNat*(width*width)+(s.regs 14).toNat)*8+output.toNat<2^64)
    (offset : Coefficients.extent width≤output.toNat) :
    (s.regs 0).toNat+Coefficients.extent width≤(CellFinal.location s width output).toNat := by
  rw [CellFinal.location_exact s hi bound nowrap]
  omega

/-- Every byte below the coefficient fence is unchanged by the actual fetched
index/store/return tail, for any stored floating-point bit pattern. -/
theorem fetched_preserves_coefficients (hi : width≤5)
    (bound : (s.core.regs 15).toNat*(width*width)+(s.core.regs 14).toNat<2^32)
    (nowrap : (s.core.regs 0).toNat+
      ((s.core.regs 15).toNat*(width*width)+(s.core.regs 14).toNat)*8+output.toNat<2^64)
    (offset : Coefficients.extent width≤output.toNat)
    (running : s.halted=false)
    (valid : Valid64 s.core.globalStart s.core.globalBytes (CellFinal.location s.core width output).toNat)
    (precode : List Kernel.Instr) (pc : s.core.pc=precode.length)
    (run : Kernel.Run ctx (precode++CellFinal.tail width output) s final)
    (p : Nat) (coefficient : p<(s.core.regs 0).toNat+Coefficients.extent width) :
    final.core.global p=s.core.global p := by
  have frame := (CellFinal.tail_correct running valid (Kernel.run_exec run precode _ rfl pc)).2.2.1
  have lower := after_coefficients s.core hi bound nowrap offset
  exact frame p (Or.inl (by omega))

/-- Distinct nonwrapping cell/lane indices address disjoint eight-byte outputs.
This is not yet a theorem that the concurrent program has one writer per index. -/
theorem distinct_outputs (a b : PTX.State) (hi : width≤5)
    (ab : (a.regs 15).toNat*(width*width)+(a.regs 14).toNat<2^32)
    (bb : (b.regs 15).toNat*(width*width)+(b.regs 14).toNat<2^32)
    (an : (a.regs 0).toNat+((a.regs 15).toNat*(width*width)+(a.regs 14).toNat)*8+output.toNat<2^64)
    (bn : (b.regs 0).toNat+((b.regs 15).toNat*(width*width)+(b.regs 14).toNat)*8+output.toNat<2^64)
    (base : a.regs 0=b.regs 0)
    (different : (a.regs 15).toNat*(width*width)+(a.regs 14).toNat≠
      (b.regs 15).toNat*(width*width)+(b.regs 14).toNat) :
    (CellFinal.location a width output).toNat+8≤(CellFinal.location b width output).toNat ∨
    (CellFinal.location b width output).toNat+8≤(CellFinal.location a width output).toNat := by
  rw [CellFinal.location_exact a hi ab an,CellFinal.location_exact b hi bb bn,base]
  omega

/-- Transfer the numerical theorem through an order-preserving event projection.
The projected arithmetic run and geometry of omitted stores are explicit inputs;
constructing them from a full concurrent tail execution is a separate obligation. -/
theorem projected_arithmetic {whole : List (Event 32)}
    (launch : Numeric.Launch width bases start) (lo : 2≤width) (hi : width≤5)
    (run : Runs cfg (program width) start events final)
    (embedding : Projection.Embedding events whole)
    (nowrap : (bases .global).toNat+Coefficients.extent width≤2^64)
    (writes : ∀ (w : Nat) (writer : Fin 32) (wa : Access), whole[w]?=some (.data writer wa) →
      wa.data.store=true → ¬Projection.Retained embedding w →
      wa.space=.global ∧ (bases .global).toNat+Coefficients.extent width≤wa.data.address)
    (compatible : Visibility.Compatible initial whole original)
    (performed : Visibility.Performed whole original)
    (thread : Fin 32) (i j : Fin width) (lane : thread.val=i.val*width+j.val)
    (finished : (final.lanes thread).pc=(program width).length) :
    decode ((final.lanes thread).regs 11)=Spec.get2 (localAction
      (Numeric.initialTensor width bases initial .global 0)
      (Numeric.initialTensor width bases initial .global (width*width*8+32))
      (Numeric.initialTensor width bases initial .global (2*(width*width*8+32)))
      (Numeric.initialTensor width bases initial .shared 0)) i j := by
  have separate := Projection.separated_by_fence embedding (fun _ reader ra observed read global =>
    (Coefficients.read_bounds launch lo hi run nowrap (List.mem_of_getElem? observed) read global).2) writes
  exact completed_run launch lo hi run (Projection.compatible embedding separate compatible)
    (Projection.performed embedding performed) thread i j lane finished

end PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.Output

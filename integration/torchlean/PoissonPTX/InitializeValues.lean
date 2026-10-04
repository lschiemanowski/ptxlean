import PoissonPTX.InitializeState
import PoissonPTX.Sources

namespace PtxTorchLean.Poisson.PTX.Initialize

def loadWord (s : State) (boundary input : Word) : Word :=
  if Assembly.maskFlag s boundary=0 then read64 s.global (address s 12 input).toNat else 0

theorem masked_word : (masked ctx s boundary input).core.regs 4=loadWord s.core boundary input := by
  simp [masked,loadLoaded,maskLoaded,loadWord,Assembly.maskLoaded,Assembly.maskFlag,Assembly.maskAddress,
    Flow.simple,Flow.next,Flow.Compare.apply,Kernel.u32,assign,advance,addressed,address,wide,Operand.eval]
  split <;> simp_all

theorem copied_global : (copied ctx s boundary input rhs r).core.global=
    write64 (write64 s.core.global (address s.core 12 rhs).toNat (loadWord s.core boundary input))
      (address s.core 12 r).toNat (loadWord s.core boundary input) := by
  simp only [copied,StorePair.finish_global (by decide : 4≠1) (by decide : 4≠2),masked_frame.1,masked_word,
    address,wide,masked_frame.2.2.2.1,masked_frame.2.2.2.2.1]

theorem ready_word : (ready ctx s boundary input rhs r diagonal).core.regs 4=loadWord s.core boundary input := by
  simp [ready,diagonalLoaded,Flow.simple,Flow.next,assign,advance,addressed,copied]
  split <;> simp [StorePair.finish_frame.2.2.2.2.2 4 (by decide) (by decide),masked_word]

theorem ready_divisor : (ready ctx s boundary input rhs r diagonal).core.regs 5=
    if Assembly.maskFlag s.core boundary=0 then
      read64 (copied ctx s boundary input rhs r).core.global (address s.core 12 diagonal).toNat
    else PreconditionUpdate.one := by
  simp only [ready,diagonalLoaded,Flow.simple,Flow.next]
  simp only [copied,masked,loadLoaded,maskLoaded,Assembly.maskLoaded,Flow.simple,Flow.next,
    Flow.Compare.apply,Operand.eval,assign,advance,addressed]
  simp [address,wide,Kernel.u32,StorePair.finish_frame.2.2.2.1,StorePair.finish_frame.2.2.2.2.1]
  split <;> simp_all [Assembly.maskFlag,Assembly.maskAddress]

def quotient (s : State) (boundary input diagonal : Word) : Float :=
  decode (loadWord s boundary input)/decode (PreconditionUpdate.divisor s diagonal boundary)

theorem ready_result
    (rhsD : Sources.Disjoint (address s.core 12 rhs).toNat (address s.core 12 diagonal).toNat)
    (rD : Sources.Disjoint (address s.core 12 r).toNat (address s.core 12 diagonal).toNat) :
    DividePair.result (ready ctx s boundary input rhs r diagonal).core=quotient s.core boundary input diagonal := by
  simp only [DividePair.result,ready_word,ready_divisor,copied_global,
    read64_write64_disjoint _ _ _ _ rD,read64_write64_disjoint _ _ _ _ rhsD,
    quotient,PreconditionUpdate.divisor]

theorem finish_global : (finish ctx s boundary input rhs r diagonal z p x value).core.global=
    write64 (write64 (write64 (write64 (write64 s.core.global
      (address s.core 12 rhs).toNat (loadWord s.core boundary input))
      (address s.core 12 r).toNat (loadWord s.core boundary input))
      (address s.core 12 z).toNat value) (address s.core 12 p).toNat value) (address s.core 12 x).toNat 0 := by
  simp only [finish,StoreZero.finish_global]
  rw [divided_address]
  simp only [divided,DividePair.finish_global,ready_address,ready_frame.1,copied_global]

end PtxTorchLean.Poisson.PTX.Initialize

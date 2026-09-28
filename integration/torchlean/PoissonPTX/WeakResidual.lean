import PoissonPTX.Weak
import PoissonPTX.Layout

namespace PtxTorchLean.Poisson.PTX.Weak.Residual
open Kernel Sources
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

/-- The only accesses produced by an active lane's actual instruction execution. -/
def accesses (ctx : Context) (s : Kernel.State) (count : BitVec 32)
    (rhs ap output a b c : Word) : List Access :=
  [⟨9,false,(address (Kernel.Residual.setup ctx s count).core 12 rhs).toNat,a⟩,
   ⟨13,false,(address (Kernel.Residual.setup ctx s count).core 12 ap).toNat,b⟩,
   ⟨18,true,(address (Kernel.Residual.setup ctx s count).core 12 output).toNat,c⟩]

def finish (ctx : Context) (s : Kernel.State) (count : BitVec 32)
    (rhs ap output a b c : Word) : Kernel.State :=
  let start := Kernel.Residual.setup ctx s count
  let left := assign (addressed start.core 12 rhs) 4 a
  let right := assign (addressed left 12 ap) 5 b
  let fp := assign right 6 c
  Kernel.halt {start with core := (put (addressed fp 12 output) .global
    (address start.core 12 output).toNat c)}

/-- An exact symbolic execution of all twenty fetched instructions, including
arbitrary load words and every allowed arithmetic output encoding. -/
theorem execution (ctx : Context) (s : Kernel.State) (count : BitVec 32)
    (rhs ap output : Word) (choose : Nat → Word)
    (pc : s.core.pc=0) (running : s.halted=false) (live : Kernel.Residual.live ctx count)
    (hr : Valid64 s.core.globalStart s.core.globalBytes (address (Kernel.Residual.setup ctx s count).core 12 rhs).toNat)
    (ha : Valid64 s.core.globalStart s.core.globalBytes (address (Kernel.Residual.setup ctx s count).core 12 ap).toNat)
    (ho : Valid64 s.core.globalStart s.core.globalBytes (address (Kernel.Residual.setup ctx s count).core 12 output).toNat) (fuel : Nat := 0) :
    execute ctx (Kernel.Residual.program count rhs ap output) choose (fuel+20) s =
      if FP.Result .sub (choose 9) (choose 13) (choose 14) then
        some (finish ctx s count rhs ap output (choose 9) (choose 13) (choose 14),
          accesses ctx s count rhs ap output (choose 9) (choose 13) (choose 14))
      else none := by
  have hn : ¬ count.toNat ≤ (Kernel.Residual.index ctx).toNat := Nat.not_le_of_gt live
  simp only [Kernel.Residual.index,BitVec.toNat_add,BitVec.toNat_mul] at hn
  norm_num at hn
  have hnneg := Nat.not_le_of_gt hn
  simp [address,wide,Kernel.Residual.setup,Kernel.simple,Kernel.scalar,Kernel.advance,
    Kernel.halt,assign,PTX.advance,u32,hnneg] at hr ha ho
  by_cases allowed : FP.Result .sub (choose 9) (choose 13) (choose 14)
  all_goals
    simp only [allowed,ite_true,ite_false]
    iterate 20
      first
      | (rw [execute]
         simp [Weak.step,instruction,data,Kernel.Residual.program,Kernel.Residual.prologue,
           PTX.Residual.code,loadCode,storeCode,addressCode,PTX.eval,Operand.eval,access,
           Kernel.simple,Kernel.scalar,Kernel.advance,Kernel.halt,assign,PTX.advance,put,
           PTX.State.start,PTX.State.bytes,PTX.State.memory,u32,pc,running,hnneg,hr,ha,ho,allowed])
      | skip
    all_goals simp [finish,accesses,Kernel.Residual.setup,addressed,address,wide,
      Kernel.simple,Kernel.scalar,Kernel.advance,Kernel.halt,assign,PTX.advance,put,
      u32,pc,running,hnneg]


end PtxTorchLean.Poisson.PTX.Weak.Residual

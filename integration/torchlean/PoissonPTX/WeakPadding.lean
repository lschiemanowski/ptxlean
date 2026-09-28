import PoissonPTX.WeakResidual

namespace PtxTorchLean.Poisson.PTX.Weak.Residual
open Kernel Sources

/-- Padded hardware lanes fetch their guard and return, contributing no memory
labels. This holds for arbitrary initial storage, choices and extra fuel. -/
theorem padding (ctx : Context) (s : Kernel.State) (count : BitVec 32)
    (rhs ap output : Word) (choose : Nat → Word) (fuel : Nat)
    (pc : s.core.pc=0) (running : s.halted=false) (inactive : ¬Kernel.Residual.live ctx count) :
    execute ctx (Kernel.Residual.program count rhs ap output) choose (fuel+6) s =
      some (Kernel.Residual.setup ctx s count,[]) := by
  have hge : count.toNat ≤ (Kernel.Residual.index ctx).toNat := Nat.le_of_not_gt inactive
  simp [Kernel.Residual.index] at hge
  iterate 6
    rw [execute]
    simp [Weak.step,instruction,Kernel.Residual.program,Kernel.Residual.prologue,
      PTX.Residual.code,loadCode,storeCode,addressCode,Kernel.simple,Kernel.scalar,
      Kernel.advance,Kernel.halt,assign,PTX.advance,u32,pc,running,hge]
  simp [Kernel.Residual.setup,Kernel.simple,Kernel.scalar,Kernel.advance,Kernel.halt,
    assign,PTX.advance,u32,pc,running,hge]

end PtxTorchLean.Poisson.PTX.Weak.Residual

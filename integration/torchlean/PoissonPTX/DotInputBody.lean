import PoissonPTX.Residual
import PoissonPTX.ControlFlow

/-! One actual strided dot-product iteration: two four-instruction global
loads, separate rounded multiplication and addition, and a 256-index step. -/
namespace PtxTorchLean.Poisson.PTX.DotInput

def body (left right : Word) : List Op :=
  loadCode 4 12 left ++ loadCode 5 12 right ++
    [.fp .mul 10 (.reg 4) (.reg 5),.fp .add 8 (.reg 8) (.reg 10),
      .add32 12 (.reg 12) (.imm 256)]

def Valid (s : State) (left right : Word) : Prop :=
  Valid64 s.globalStart s.globalBytes (address s 12 left).toNat ∧
  Valid64 s.globalStart s.globalBytes (address s 12 right).toNat

def product (s : State) (left right : Word) : Float :=
  decode (read64 s.global (address s 12 left).toNat) *
  decode (read64 s.global (address s 12 right).toNat)

def Stable (s t : State) : Prop :=
  t.global=s.global ∧ t.shared=s.shared ∧ t.globalStart=s.globalStart ∧ t.globalBytes=s.globalBytes ∧
  t.sharedStart=s.sharedStart ∧ t.sharedBytes=s.sharedBytes ∧
  t.regs 0=s.regs 0 ∧ t.regs 3=s.regs 3 ∧ t.regs 14=s.regs 14

def loaded (s : State) (left right : Word) : State := Residual.right s left right

theorem loads (s : State) (valid : Valid s left right) :
    run (loadCode 4 12 left ++ loadCode 5 12 right) s=some (loaded s left right) := by
  rw [run_append,load_run s 4 12 left valid.1]
  change run (loadCode 5 12 right) (Residual.left s left)=some (loaded s left right)
  have h := load_run (Residual.left s left) 5 12 right
    (by simpa [Residual.left,assign,advance,addressed,address,wide] using valid.2)
  simpa [loaded,Residual.right,Residual.left,assign,advance,addressed,address,wide] using h

theorem loaded_eq (run : Block (loadCode 4 12 left ++ loadCode 5 12 right) s t)
    (valid : Valid s left right) : t=loaded s left right := by
  have complete := block_complete run (by simp [loadCode,addressCode,noFP])
  rw [loads s valid] at complete
  exact (Option.some.inj complete).symm

theorem correct (execution : Block (body left right) s t) (valid : Valid s left right) :
    decode (t.regs 8)=decode (s.regs 8)+product s left right ∧
    t.regs 12=add32 (s.regs 12) 256 ∧ Stable s t := by
  obtain ⟨middle,read,rest⟩ := block_split (loadCode 4 12 left ++ loadCode 5 12 right)
    _ (by simpa [body,List.append_assoc] using execution)
  have same := loaded_eq read valid
  subst middle
  cases rest with | cons multiply rest =>
    cases multiply with | fp productResult =>
      cases rest with | cons add rest =>
        cases add with | fp sumResult =>
          cases rest with | cons increment rest =>
            cases increment
            cases rest
            simp only [FP.Result,FP.apply,Operand.eval] at productResult sumResult
            simp [loaded,Residual.right,Residual.left,assign,advance,addressed,address,wide] at productResult sumResult ⊢
            exact ⟨by simpa [product,address,wide,productResult] using sumResult,rfl,by simp [Stable]⟩

theorem exists_execution (s : State) (valid : Valid s left right) :
    ∃ t, Block (body left right) s t := by
  let ready := loaded s left right
  obtain ⟨prod,hprod⟩ := FP.result_exists .mul (ready.regs 4) (ready.regs 5)
  let multiplied := assign ready 10 prod
  obtain ⟨sum,hsum⟩ := FP.result_exists .add (multiplied.regs 8) (multiplied.regs 10)
  let added := assign multiplied 8 sum
  refine ⟨assign added 12 (add32 (added.regs 12) 256),?_⟩
  apply block_append (run_sound (loads s valid))
  exact .cons (.fp hprod) (.cons (.fp hsum) (.cons .add32 .nil))

def cursor (s : State) : Nat := (Kernel.u32 (s.regs 12)).toNat

theorem progress (inside : cursor s<count) (bounded : count<2^30)
    (updated : t.regs 12=add32 (s.regs 12) 256) : cursor t=cursor s+256 := by
  have small : cursor s+256<4294967296 := by omega
  simpa [cursor,updated,Kernel.u32,add32,BitVec.toNat_add,BitVec.toNat_setWidth,
    Nat.mod_mod_of_dvd _ (by decide : 4294967296 ∣ 18446744073709551616)] using Nat.mod_eq_of_lt small

end PtxTorchLean.Poisson.PTX.DotInput

import Ptx.MulHi32
import Ptx.Bfe32

-- Check the exact arithmetic used in the two false multiplication findings.
example : (-1 : Int) / (2^32 : Int) = -1 := by decide
example : Ptx.Scalar.MulHi32.compute .signed 1 0xffffffff = 0xffffffff := by decide
example : Ptx.Scalar.MulHi32.compute .signed 0xffffffff 1 = 0xffffffff := by decide

-- Check extraction at the reviewer's large position, both signednesses.
example : Ptx.Scalar.Bfe32.compute .unsigned 0xffffffff 256 1 = 1 := by decide
example : Ptx.Scalar.Bfe32.compute .signed 0xffffffff 256 1 = 0xffffffff := by decide
example : Ptx.Scalar.Bfe32.compute .unsigned 5 0 4 = 5 := by decide
example : Ptx.Scalar.Bfe32.Text.decode
    ⟨.always, "bfe.u32", [.word (.reg 0), .word (.imm 5), .word (.imm 0), .word (.imm 4)]⟩ =
    .ok (⟨.always, .unsigned, 0, .imm 5, .imm 0, .imm 4⟩ : Ptx.Scalar.Bfe32.Instr) := by rfl

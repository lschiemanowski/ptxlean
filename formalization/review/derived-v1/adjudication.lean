import Ptx.Pure32

-- The reviewer correctly identified swapped LOP3 table weights, but its proposed
-- AND-table counterexample is false: both selected bits of 0x80 are zero.
example : (0x80 : BitVec 8).getLsbD 4 = false := by decide
example : (0x80 : BitVec 8).getLsbD 1 = false := by decide

-- A first-input projection table distinguishes the same two indices.
example : (0xf0 : BitVec 8).getLsbD 4 = true := by decide
example : (0xf0 : BitVec 8).getLsbD 1 = false := by decide

-- For insertion, the reviewer's input position 256 denotes position zero.
example : (256 : BitVec 32).toNat % 256 = 0 := by decide
example : ¬ (256 : Nat) ≤ 0 := by decide

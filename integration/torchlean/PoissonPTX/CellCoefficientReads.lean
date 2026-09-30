import PoissonPTX.CellCoefficientProgram

namespace PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.Coefficients
open CellMiddle Symbolic

/-- Actual coefficient addresses, including the last byte, are bounded without
any hypothesis about the values chosen by candidate loads. -/
theorem read_bounds {events : List (Event 32)} {reader : Fin 32} {access : Access}
    (launch : Numeric.Launch width bases start) (lo : 2≤width) (hi : width≤5)
    (run : Runs cfg (program width) start events final)
    (nowrap : (bases .global).toNat+extent width≤2^64)
    (member : Event.data reader access∈events) (read : access.data.store=false)
    (global : access.space=.global) :
    (bases .global).toNat≤access.data.address ∧
      access.data.address+8≤(bases .global).toNat+extent width := by
  have live := active launch lo hi run member
  obtain ⟨before,op,next,fetch,hd,hregs⟩ := Symbolic.access_registers run launch.aligned
    (symbolic launch .addresses (fun _ _ => 0)) (guards width lo hi) (by intro h; cases h) member live
  obtain ⟨sp,dst,addr,rfl,space,pc,address,valid,result⟩ := load_origin hd read
  have sg : sp=.global := space.symm.trans global
  subst sp
  have fetch' : (program width)[access.data.pc]?=some (.data (.load64 .global dst addr)) := by rw [pc]; simpa [global] using fetch
  obtain ⟨hp,_⟩ := List.getElem?_eq_some_iff.mp fetch'
  have cert := checked width lo hi ⟨reader.val,live⟩ ⟨access.data.pc,hp⟩
  simp only [checkAt,fetch'] at cert
  have related := operand_sound hregs addr
  cases he : Numeric.extract (operand (atPC .addresses (program width) (Numeric.seed width reader.val) access.data.pc) addr) with
  | none => simp [he] at cert
  | some pair =>
    obtain ⟨sp,off⟩ := pair
    cases sp with
    | shared => simp [he] at cert
    | global =>
      simp only [he] at cert
      have natural : access.data.address=(bases .global).toNat+off.toNat := by
        rw [address,Numeric.extract_sound related he,BitVec.toNat_add,Nat.mod_eq_of_lt (by omega)]
      rw [natural]
      constructor <;> omega

end PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.Coefficients

import PoissonPTX.AssemblyArenaSafety

namespace PtxTorchLean.Poisson.PTX.Assembly

def Arena.entryIndex (a : Arena n) (memory : Memory) (k : Nat) : Nat :=
  (read32 memory (a.base.toNat+a.entries.toNat+k*4)).toNat

def Arena.elementValue (a : Arena n) (memory : Memory) (k : Nat) : Float :=
  decode (read64 memory (a.base.toNat+a.element.toNat+k*8))

def Arena.row (a : Arena n) (memory : Memory) (i : Fin n) : List Nat :=
  (List.range' (a.offset memory i.val) (a.offset memory (i.val+1)-a.offset memory i.val)).map (a.entryIndex memory)

def Arena.value (a : Arena n) (memory : Memory) (i : Fin n) (mask : Bool) : Float :=
  if mask=true ∧ read32 memory (a.base.toNat+a.boundary.toNat+i.val*4)≠0 then 0 else
    (a.row memory i).foldl (fun acc k => acc+a.elementValue memory k) 0

theorem Arena.contribution_value (a : Arena n) (memory : Memory) (regs : Registers) (i : Fin n)
    (contents : a.Contents memory) (k : Nat) (inside : k<a.entryCount) :
    contribution (ready (a.context i) (BitVec.ofNat 32 n) a.offsets (a.start memory regs)).core a.entries a.element k=
      a.elementValue memory (a.entryIndex memory k) := by
  let initial := (ready (a.context i) (BitVec.ofNat 32 n) a.offsets (a.start memory regs)).core
  have small : k<2^32 := lt_trans inside a.entriesSmall
  have current : Kernel.u32 ((atCursor initial k).regs 19)=BitVec.ofNat 32 k := by simp [atCursor,Kernel.u32]
  have base : initial.regs 0=a.base := by simp [initial,ready,prepared,setup,Arena.context]
  have mem : initial.global=memory := rfl
  have idxAddress : (indexAddress (atCursor initial k) a.entries).toNat=a.base.toNat+a.entries.toNat+k*4 := by
    unfold indexAddress
    rw [current]
    change (address32 (initial.regs 0) (BitVec.ofNat 32 k) a.entries).toNat=_
    rw [base,address32_exact _ _ _ (by
      rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt small]
      have := a.entriesFit; have := a.noWrap; omega)]
    rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt small]
    omega
  have idx : (Assembly.index (atCursor initial k) a.entries).toNat=a.entryIndex memory k := by
    change (read32 initial.global (indexAddress (atCursor initial k) a.entries).toNat).toNat=_
    rw [idxAddress,mem]
    rfl
  have bound := contents.indices k inside
  change a.entryIndex memory k<a.elementCount at bound
  have valAddress : (valueAddress (atCursor initial k) a.entries a.element).toNat=
      a.base.toNat+a.element.toNat+(a.entryIndex memory k)*8 := by
    unfold valueAddress
    change (address64 (initial.regs 0) (Assembly.index (atCursor initial k) a.entries) a.element).toNat=_
    rw [base,address64_exact _ _ _ (by rw [idx]; have := a.elementFit; have := a.noWrap; omega),idx]
    omega
  change decode (read64 initial.global (valueAddress (atCursor initial k) a.entries a.element).toNat)=_
  rw [valAddress,mem]
  rfl

/-- Reduce the machine's result expression to the ordered physical row. All
index and floating-point values are read from initial memory. -/
theorem Arena.value_eq (a : Arena n) (memory : Memory) (regs : Registers) (i : Fin n)
    (contents : a.Contents memory) (mask : Bool) :
    entryValue (a.context i) (BitVec.ofNat 32 n) a.offsets a.entries a.element mask a.boundary (a.start memory regs)=
      a.value memory i mask := by
  unfold entryValue Arena.value
  simp only [maskFlag,a.boundary_address,a.ready_cursor,a.ready_limit]
  change (if mask=true ∧ read32 memory (a.base.toNat+a.boundary.toNat+i.val*4)≠0 then _ else _)=_
  split <;> rename_i selected
  · simp [selected]
  · simp only [selected,↓reduceIte,Arena.row,List.foldl_map]
    have fold {f g : Nat → Float} : ∀ (xs : List Nat) (acc : Float),
        (∀ k∈xs, f k=g k) → xs.foldl (fun acc k => acc+f k) acc=xs.foldl (fun acc k => acc+g k) acc := by
      intro xs
      induction xs with
      | nil => intro acc _; rfl
      | cons k xs ih =>
        intro acc same
        simp only [List.foldl_cons]
        rw [same k (by simp)]
        exact ih _ (fun j member => same j (by simp [member]))
    apply fold
    intro k member
    have range := List.mem_range'.mp member
    have ordered := contents.ordered i.val i.isLt
    have last := contents.last i.val i.isLt
    rw [a.contribution_value memory regs i contents k (by omega)]

end PtxTorchLean.Poisson.PTX.Assembly

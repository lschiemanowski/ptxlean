import PoissonPTX.ScalarLoad

namespace PtxTorchLean.Poisson.PTX.AffineUpdate

/-- The update_p body: beta is a scalar field; p and z use register 12's
vector index. Separate mul/add instructions preserve the emitted rounding order. -/
def code (coefficient input shift output : Word) : List Op :=
  ScalarLoad.code 4 coefficient ++ loadCode 5 12 input ++ loadCode 6 12 shift ++
    [.fp .mul 10 (.reg 4) (.reg 5),.fp .add 6 (.reg 6) (.reg 10)] ++ storeCode 6 12 output

def scalar (s : State) (coefficient : Word) : State := ScalarLoad.loaded s 4 coefficient

def left (s : State) (coefficient input : Word) : State :=
  assign (addressed (scalar s coefficient) 12 input) 5 (read64 s.global (address s 12 input).toNat)

def loaded (s : State) (coefficient input shift : Word) : State :=
  assign (addressed (left s coefficient input) 12 shift) 6 (read64 s.global (address s 12 shift).toNat)

def product (s : State) (coefficient input : Word) : Float :=
  decode (read64 s.global (s.regs 0+coefficient).toNat)*decode (read64 s.global (address s 12 input).toNat)

def result (s : State) (coefficient input shift : Word) : Float :=
  decode (read64 s.global (address s 12 shift).toNat)+product s coefficient input

def finish (s : State) (coefficient input shift output mulWord value : Word) : State :=
  put (addressed (assign (assign (loaded s coefficient input shift) 10 mulWord) 6 value) 12 output)
    .global (address s 12 output).toNat value

/-- All loads precede the first write, including when output aliases input. -/
theorem load_executes (s : State) (coefficient input shift : Word)
    (hc : Valid64 s.globalStart s.globalBytes (s.regs 0+coefficient).toNat)
    (hi : Valid64 s.globalStart s.globalBytes (address s 12 input).toNat)
    (hz : Valid64 s.globalStart s.globalBytes (address s 12 shift).toNat) :
    Block (ScalarLoad.code 4 coefficient ++ loadCode 5 12 input ++ loadCode 6 12 shift) s
      (loaded s coefficient input shift) := by
  have first := run_sound (ScalarLoad.executes s 4 coefficient hc)
  have second := run_sound (load_run (scalar s coefficient) 5 12 input
    (by simpa [scalar,ScalarLoad.loaded,ScalarLoad.addressed,assign,advance,address,wide] using hi))
  have third := run_sound (load_run (left s coefficient input) 6 12 shift
    (by simpa [left,scalar,ScalarLoad.loaded,ScalarLoad.addressed,assign,advance,addressed,address,wide] using hz))
  have second' : Block (loadCode 5 12 input) (scalar s coefficient) (left s coefficient input) := by
    simpa [left,scalar,ScalarLoad.loaded,ScalarLoad.addressed,assign,advance,address,wide] using second
  have third' : Block (loadCode 6 12 shift) (left s coefficient input) (loaded s coefficient input shift) := by
    simpa [loaded,left,scalar,ScalarLoad.loaded,ScalarLoad.addressed,assign,advance,addressed,address,wide] using third
  exact block_append (block_append first second') third'

theorem loads_eq (actual : Block (ScalarLoad.code 4 coefficient ++ loadCode 5 12 input ++ loadCode 6 12 shift) s final)
    (hi : Valid64 s.globalStart s.globalBytes (address s 12 input).toNat)
    (hz : Valid64 s.globalStart s.globalBytes (address s 12 shift).toNat) : final=loaded s coefficient input shift := by
  obtain ⟨a,first,rest⟩ := block_split (ScalarLoad.code 4 coefficient) (loadCode 5 12 input ++ loadCode 6 12 shift)
    (by simpa [List.append_assoc] using actual)
  have same := ScalarLoad.block_eq first
  subst a
  obtain ⟨b,second,third⟩ := block_split (loadCode 5 12 input) (loadCode 6 12 shift) rest
  have same : b=left s coefficient input := by
    simpa [left,scalar,ScalarLoad.loaded,ScalarLoad.addressed,assign,advance,address,wide] using
      load_block_eq second (by simpa [ScalarLoad.loaded,ScalarLoad.addressed,assign,advance,address,wide] using hi)
  subst b
  simpa [loaded,left,scalar,ScalarLoad.loaded,ScalarLoad.addressed,assign,advance,addressed,address,wide] using
    load_block_eq third (by simpa [left,scalar,ScalarLoad.loaded,ScalarLoad.addressed,assign,advance,addressed,address,wide] using hz)

end PtxTorchLean.Poisson.PTX.AffineUpdate

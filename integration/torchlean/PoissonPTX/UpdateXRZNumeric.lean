import PoissonPTX.UpdateXRZMemory

namespace PtxTorchLean.Poisson.PTX.UpdateXRZ

/-- Physical separation needed between earlier writes and later inputs, and
between the three final outputs. All conditions are on initial addresses. -/
structure Separate (s : State) (x ap r diagonal boundary z : Word) : Prop where
  xAP : Sources.Disjoint (address s 12 x).toNat (address s 12 ap).toNat
  xR : Sources.Disjoint (address s 12 x).toNat (address s 12 r).toNat
  xD : Sources.Disjoint (address s 12 x).toNat (address s 12 diagonal).toNat
  rD : Sources.Disjoint (address s 12 r).toNat (address s 12 diagonal).toNat
  xZ : Sources.Disjoint (address s 12 x).toNat (address s 12 z).toNat
  rZ : Sources.Disjoint (address s 12 r).toNat (address s 12 z).toNat
  xB : (address s 12 x).toNat+8≤(Assembly.maskAddress s boundary).toNat ∨
    (Assembly.maskAddress s boundary).toNat+4≤(address s 12 x).toNat
  rB : (address s 12 r).toNat+8≤(Assembly.maskAddress s boundary).toNat ∨
    (Assembly.maskAddress s boundary).toNat+4≤(address s 12 r).toNat

def alphaValue (s : State) (alpha : Word) : Float := decode (read64 s.global (s.regs 0+alpha).toNat)
def vectorValue (s : State) (field : Word) : Float := decode (read64 s.global (address s 12 field).toNat)
def xValue (s : State) (alpha p x : Word) : Float := vectorValue s x+alphaValue s alpha*vectorValue s p
def rValue (s : State) (alpha ap r : Word) : Float := vectorValue s r-alphaValue s alpha*vectorValue s ap
def zValue (s : State) (alpha ap r diagonal boundary : Word) : Float :=
  rValue s alpha ap r/decode (PreconditionUpdate.divisor s diagonal boundary)

theorem x_value : RegisterUpdate.result .add (coefficient s alpha).core p x=xValue s.core alpha p x := by
  simp only [RegisterUpdate.result,RegisterUpdate.product,coefficient_global,coefficient_geometry.address,
    coefficient_word,FP.apply,xValue,vectorValue,alphaValue]

theorem r_value (separated : Separate s.core x ap r diagonal boundary z) :
    RegisterUpdate.result .sub (solution s alpha p x xm xv).core ap r=rValue s.core alpha ap r := by
  simp only [RegisterUpdate.result,RegisterUpdate.product,solution_global,solution_geometry.address,
    solution_word,FP.apply,rValue,vectorValue,alphaValue]
  rw [read64_write64_disjoint _ _ _ _ separated.xR,read64_write64_disjoint _ _ _ _ separated.xAP]

theorem divisor_value (separated : Separate s.core x ap r diagonal boundary z) :
    PreconditionUpdate.divisor (residual s alpha p x ap r xm xv rm rv).core diagonal boundary=
      PreconditionUpdate.divisor s.core diagonal boundary := by
  unfold PreconditionUpdate.divisor Assembly.maskFlag
  rw [residual_geometry.mask,residual_geometry.address,residual_global]
  rw [read32_write64_disjoint _ _ _ _ separated.rB,read32_write64_disjoint _ _ _ _ separated.xB]
  rw [read64_write64_disjoint _ _ _ _ separated.rD,read64_write64_disjoint _ _ _ _ separated.xD]

theorem z_value (separated : Separate s.core x ap r diagonal boundary z)
    (rWord : decode rv=rValue s.core alpha ap r) :
    PreconditionUpdate.result (residual s alpha p x ap r xm xv rm rv).core diagonal boundary=
      zValue s.core alpha ap r diagonal boundary := by
  simp only [PreconditionUpdate.result,residual_word,divisor_value separated,rWord,zValue]

/-- The three stored words remain at their distinct output slots after all
writes, with no assumption about their desired values. -/
theorem stored_words (separated : Separate s.core x ap r diagonal boundary z) :
    read64 (finish ctx s alpha p x ap r diagonal boundary z xm xv rm rv zv).core.global (address s.core 12 x).toNat=xv ∧
    read64 (finish ctx s alpha p x ap r diagonal boundary z xm xv rm rv zv).core.global (address s.core 12 r).toNat=rv ∧
    read64 (finish ctx s alpha p x ap r diagonal boundary z xm xv rm rv zv).core.global (address s.core 12 z).toNat=zv := by
  rw [finish_global]
  have zx : Sources.Disjoint (address s.core 12 z).toNat (address s.core 12 x).toNat := separated.xZ.symm
  have rx : Sources.Disjoint (address s.core 12 r).toNat (address s.core 12 x).toNat := separated.xR.symm
  have zr : Sources.Disjoint (address s.core 12 z).toNat (address s.core 12 r).toNat := separated.rZ.symm
  rw [read64_write64_disjoint _ _ _ _ zx,read64_write64_disjoint _ _ _ _ rx,
    read64_write64_disjoint _ _ _ _ zr]
  simp

end PtxTorchLean.Poisson.PTX.UpdateXRZ

import PoissonPTX.UpdateXRZ

namespace PtxTorchLean.Poisson.PTX.UpdateXRZ

/-- The immutable part of the local address geometry. -/
def SameGeometry (s t : State) : Prop :=
  t.globalStart=s.globalStart ∧ t.globalBytes=s.globalBytes ∧ t.regs 0=s.regs 0 ∧ t.regs 12=s.regs 12

def Valid (s : State) (alpha p x ap r diagonal boundary z : Word) : Prop :=
  Valid64 s.globalStart s.globalBytes (s.regs 0+alpha).toNat ∧
  (∀ field∈[p,x,ap,r,diagonal,z], Valid64 s.globalStart s.globalBytes (address s 12 field).toNat) ∧
  Valid32 s.globalStart s.globalBytes (Assembly.maskAddress s boundary).toNat

theorem SameGeometry.address (same : SameGeometry s t) : address t 12 field=address s 12 field := by
  simp [PTX.address,wide,same.2.2.1,same.2.2.2]

theorem SameGeometry.mask (same : SameGeometry s t) : Assembly.maskAddress t boundary=Assembly.maskAddress s boundary := by
  simp [Assembly.maskAddress,same.2.2.1,same.2.2.2]

theorem SameGeometry.valid (same : SameGeometry s t) (valid : Valid s alpha p x ap r diagonal boundary z) :
    Valid t alpha p x ap r diagonal boundary z := by
  simpa only [Valid,same.1,same.2.1,same.2.2.1,same.address,same.mask] using valid

theorem coefficient_geometry : SameGeometry s.core (coefficient s alpha).core := by
  simp [SameGeometry,coefficient,ScalarLoad.loaded,ScalarLoad.addressed,assign,advance]

theorem solution_geometry : SameGeometry s.core (solution s alpha p x xm xv).core := by
  simp [SameGeometry,solution,coefficient,ScalarLoad.loaded,ScalarLoad.addressed,
    RegisterUpdate.finish,RegisterUpdate.loaded,RegisterUpdate.left,put,assign,advance,addressed]

theorem residual_geometry : SameGeometry s.core (residual s alpha p x ap r xm xv rm rv).core := by
  simp [SameGeometry,residual,solution,coefficient,ScalarLoad.loaded,ScalarLoad.addressed,
    RegisterUpdate.finish,RegisterUpdate.loaded,RegisterUpdate.left,put,assign,advance,addressed]

end PtxTorchLean.Poisson.PTX.UpdateXRZ

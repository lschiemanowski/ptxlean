import Ptx.Select32
example : Ptx.Scalar.Select32.compute 7 9 true = 7 := by decide
example : (match Ptx.Scalar.Select32.Text.decode ⟨.always, "selp.b32", []⟩ with | .error (.invalidOperands _) => true | _ => false) = true := by decide

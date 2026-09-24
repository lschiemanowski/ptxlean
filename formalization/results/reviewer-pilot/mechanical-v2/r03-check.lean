import Ptx.Select32
example : (match Ptx.Scalar.Select32.Text.decode ⟨.always, "selp.b32", []⟩ with | .error (.invalidOperands _) => true | _ => false) = true := by decide

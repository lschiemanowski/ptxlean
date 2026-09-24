import Ptx.Select32
example : Ptx.Scalar.Select32.Text.decode ⟨.always, "selp.b32", []⟩ = .error (.invalidOperands "selp.b32") := by decide

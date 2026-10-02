import PoissonPTX.BarrierSources

namespace PtxTorchLean.Poisson.PTX.Concurrent.SourceCheck

def byteCompatible (initial : Space → Memory) (events : List (Event n))
    (space : Space) (address : Nat) (value : Word) (k : Fin 8) : Sources.Origin Nat → Prop
  | .initial => byte value k.val=initial space (address+k.val)
  | .store w j => match events[w]? with
    | some (.data _ access) => access.data.store=true ∧ access.space=space ∧
        access.data.address+j.val=address+k.val ∧ byte value k.val=byte access.data.value j.val
    | _ => False

instance {address : Nat} : Decidable (byteCompatible initial events space address value k origin) := by
  unfold byteCompatible
  split <;> try infer_instance
  split <;> infer_instance

/-- Finite checking of the existing per-byte compatibility relation. This does
not check the distinct performed-write relation or full PTX admission. -/
def Checked (initial : Space → Memory) (events : List (Event n))
    (source : Nat → Fin 8 → Sources.Origin Nat) : Prop :=
  ∀ r : Fin events.length, match events[r.val] with
    | .barrier _ => True
    | .data _ access => access.data.store=false → ∀ k : Fin 8,
        byteCompatible initial events access.space access.data.address access.data.value k (source r.val k)

instance : Decidable (Checked initial events source) := by
  unfold Checked
  have : ∀ r : Fin events.length, Decidable (match events[r.val] with
      | .barrier _ => True
      | .data _ access => access.data.store=false → ∀ k : Fin 8,
        byteCompatible initial events access.space access.data.address access.data.value k (source r.val k)) := by
    intro r
    split <;> infer_instance
  infer_instance

/-- A successful finite check certifies the quantified compatibility contract. -/
theorem sound (checked : Checked initial events source) : Visibility.Compatible initial events source := by
  intro r reader ra observed read k
  obtain ⟨bound,atIndex⟩ := List.getElem?_eq_some_iff.mp observed
  have checked := checked ⟨r,bound⟩
  simp only [atIndex] at checked
  have h := checked read k
  cases hs : source r k with
  | initial => simpa only [hs,byteCompatible] using h
  | store w j =>
    simp only [hs,byteCompatible] at h
    cases event : events[w]? with
    | none => simp [event] at h
    | some e => cases e with
      | barrier => simp [event] at h
      | data writer wa =>
        simp only [event] at h
        exact ⟨writer,wa,event,h⟩

end PtxTorchLean.Poisson.PTX.Concurrent.SourceCheck

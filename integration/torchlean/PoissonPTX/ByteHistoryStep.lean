import PoissonPTX.ByteHistoryReads
import PoissonPTX.ConcurrentLocalBlock

namespace PtxTorchLean.Poisson.PTX.Concurrent.ByteHistory

def ValidOp (op : Op) (s : PTX.State) : Prop :=
  match op with
  | .load64 space _ address | .store64 space address _ =>
      Valid64 (s.start space) (s.bytes space) (address.eval s).toNat
  | _ => True

/-- Supply actual earlier published bytes to a candidate load. Every store
still changes the real selected thread state and emits its actual value. -/
theorem data_exists (op : Op) (s : PTX.State) (memory : Space → Memory) (valid : ValidOp op s) :
    ∃ next access, Data op s next access ∧
      ∀ a, access=some a → a.data.store=false → a.data.value=read64 (memory a.space) a.data.address := by
  cases op with
  | load64 space dst address => exact ⟨_,_,.load (word:=read64 (memory space) (address.eval s).toNat) valid,by intro a same _; cases same; rfl⟩
  | store64 space address src => exact ⟨_,_,.store valid,by intro a same read; cases same; simp at read⟩
  | fp op dst a b =>
    obtain ⟨word,allowed⟩ := FP.result_exists op (a.eval s) (b.eval s)
    exact ⟨_,none,.ordinary rfl (.fp allowed),by simp⟩
  | _ => exact ⟨_,none,.ordinary rfl (by constructor),by simp⟩

theorem data_recorded (values : ∀ a, access=some a → a.data.store=false →
    a.data.value=read64 (memory a.space) a.data.address) (thread : Fin n) :
    Recorded memory (access.toList.map (Event.data thread)) := by
  cases access with
  | none => exact .nil
  | some a => exact .cons (values a rfl) .nil

theorem data_allocation (actual : Data op s next access) :
    next.start=s.start ∧ next.bytes=s.bytes := by
  cases actual with
  | ordinary _ actual =>
    cases actual <;> try exact ⟨rfl,rfl⟩
    cases ‹Space› <;> exact ⟨rfl,rfl⟩
  | load => exact ⟨rfl,rfl⟩
  | store => cases ‹Space› <;> exact ⟨rfl,rfl⟩

end PtxTorchLean.Poisson.PTX.Concurrent.ByteHistory

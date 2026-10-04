import PoissonPTX.MemoryBlocks

namespace PtxTorchLean.Poisson.PTX.StorePair

/-- Store the same register word twice, preserving its actual encoding. -/
def code (src : Nat) (first second : Word) : List Op := storeCode src 12 first++storeCode src 12 second

def first (s : State) (src : Nat) (offset : Word) : State :=
  put (addressed s 12 offset) .global (address s 12 offset).toNat (s.regs src)

def finish (s : State) (src : Nat) (a b : Word) : State := first (first s src a) src b

theorem executes (s : State) (src : Nat) (a b : Word) (h1 : src≠1) (h2 : src≠2)
    (ha : Valid64 s.globalStart s.globalBytes (address s 12 a).toNat)
    (hb : Valid64 s.globalStart s.globalBytes (address s 12 b).toNat) :
    run (code src a b) s=some (finish s src a b) := by
  rw [code,run_append,store_run s src 12 a h1 h2 ha]
  exact store_run (first s src a) src 12 b h1 h2
    (by simpa [first,put,addressed,assign,advance,address,wide] using hb)

theorem block_eq (actual : Block (code src a b) s t) (h1 : src≠1) (h2 : src≠2)
    (ha : Valid64 s.globalStart s.globalBytes (address s 12 a).toNat)
    (hb : Valid64 s.globalStart s.globalBytes (address s 12 b).toNat) : t=finish s src a b :=
  Option.some.inj ((block_complete actual (by simp [code,storeCode,addressCode,noFP])).symm.trans (executes s src a b h1 h2 ha hb))

theorem finish_global (h1 : src≠1) (h2 : src≠2) : (finish s src a b).global=
    write64 (write64 s.global (address s 12 a).toNat (s.regs src)) (address s 12 b).toNat (s.regs src) := by
  simp [finish,first,put,addressed,assign,advance,address,wide,h1,h2]

theorem finish_frame : (finish s src a b).globalStart=s.globalStart ∧
    (finish s src a b).globalBytes=s.globalBytes ∧ (finish s src a b).shared=s.shared ∧
    (finish s src a b).regs 0=s.regs 0 ∧ (finish s src a b).regs 12=s.regs 12 ∧
    (∀ reg, reg≠1 → reg≠2 → (finish s src a b).regs reg=s.regs reg) := by
  simp [finish,first,put,addressed,assign,advance]
  intro reg h1 h2
  simp [h1,h2]

end PtxTorchLean.Poisson.PTX.StorePair

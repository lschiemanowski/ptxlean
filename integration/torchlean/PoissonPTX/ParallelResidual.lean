import PoissonPTX.WeakResidual

namespace PtxTorchLean.Poisson.PTX.Weak.Residual.Parallel
open Kernel Sources

/-- Launch inputs and geometric validity. No field concerns computed values.
This slice represents active lanes; padding lanes are handled separately. -/
structure Inputs (n : Nat) where
  context : Fin n → Context
  start : Fin n → Kernel.State
  initial : Memory
  count : BitVec 32
  rhs : Word
  ap : Word
  output : Word
  pc : ∀ i, (start i).core.pc=0
  running : ∀ i, (start i).halted=false
  live : ∀ i, Kernel.Residual.live (context i) count
  memory : ∀ i, (start i).core.global=initial
  valid : ∀ i, ∀ off ∈ [rhs,ap,output],
    Valid64 (start i).core.globalStart (start i).core.globalBytes
      (address (Kernel.Residual.setup (context i) (start i) count).core 12 off).toNat

def Inputs.addr (p : Inputs n) (i : Fin n) (off : Word) : Nat :=
  (address (Kernel.Residual.setup (p.context i) (p.start i) p.count).core 12 off).toNat

/-- A successful candidate supplies instruction choices and actual executions;
it supplies neither source validity nor correctness of any output. -/
structure Candidate (p : Inputs n) where
  choose : Fin n → Nat → Word
  final : Fin n → Kernel.State
  trace : Fin n → List Access
  run : ∀ i, execute (p.context i) (Kernel.Residual.program p.count p.rhs p.ap p.output)
    (choose i) 20 (p.start i) = some (final i, trace i)

/-- Exact trace and primitive arithmetic are derived from all fetched instructions. -/
theorem characterize (p : Inputs n) (c : Candidate p) (i : Fin n) :
    FP.Result .sub (c.choose i 9) (c.choose i 13) (c.choose i 14) ∧
    c.trace i = accesses (p.context i) (p.start i) p.count p.rhs p.ap p.output
      (c.choose i 9) (c.choose i 13) (c.choose i 14) := by
  have h := c.run i
  rw [execution _ _ _ _ _ _ _ (p.pc i) (p.running i) (p.live i)
    (p.valid i p.rhs (by simp)) (p.valid i p.ap (by simp)) (p.valid i p.output (by simp))] at h
  split at h
  · rename_i allowed
    exact ⟨allowed, (congrArg Prod.snd (Option.some.inj h)).symm⟩
  · contradiction

/-- The three labels are exactly the executed trace, as characterize proves.
Read and store values remain arbitrary choices until source checking. -/
def events (p : Inputs n) (c : Candidate p) (e : Fin n × Fin 3) : Access :=
  match e.2.val with
  | 0 => ⟨9,false,p.addr e.1 p.rhs,c.choose e.1 9⟩
  | 1 => ⟨13,false,p.addr e.1 p.ap,c.choose e.1 13⟩
  | _ => ⟨18,true,p.addr e.1 p.output,c.choose e.1 14⟩

theorem trace_exact (p : Inputs n) (c : Candidate p) (i : Fin n) :
    c.trace i = [events p c (i,0), events p c (i,1), events p c (i,2)] := by
  simpa [events,accesses,Inputs.addr] using (characterize p c i).2

theorem store_origin (h : (events p c e).store=true) :
    e.2=2 ∧ (events p c e).address=p.addr e.1 p.output := by
  rcases e with ⟨i,k⟩
  fin_cases k <;> simp_all [events]

/-- Read-only follows from every actual store's footprint and array separation.
It is not supplied as an assumed value for any instruction. -/
theorem inputs_readonly (p : Inputs n) (c : Candidate p)
    (separated : ∀ i j, Sources.Disjoint (p.addr j p.output) (p.addr i p.rhs) ∧
      Sources.Disjoint (p.addr j p.output) (p.addr i p.ap)) (i : Fin n) :
    ReadOnly (events p c) (p.addr i p.rhs) ∧ ReadOnly (events p c) (p.addr i p.ap) := by
  constructor
  · apply readonly_of_disjoint
    intro w hw
    rw [(store_origin hw).2]
    exact (separated i w.1).1
  · apply readonly_of_disjoint
    intro w hw
    rw [(store_origin hw).2]
    exact (separated i w.1).2

/-- Universal parallel arithmetic result under only necessary byte-source
constraints. Arbitrary cross-thread ordering and torn source choices are allowed. -/
theorem stored_value (p : Inputs n) (c : Candidate p)
    (source : (Fin n × Fin 3) → Fin 8 → Origin (Fin n × Fin 3))
    (compatible : Compatible p.initial (events p c) source)
    (separated : ∀ i j, Sources.Disjoint (p.addr j p.output) (p.addr i p.rhs) ∧
      Sources.Disjoint (p.addr j p.output) (p.addr i p.ap)) (i : Fin n) :
    decode (events p c (i,2)).value =
      decode (read64 p.initial (p.addr i p.rhs)) - decode (read64 p.initial (p.addr i p.ap)) := by
  have readonly := inputs_readonly p c separated i
  have left := read_only_value (r := (i,0)) compatible (by rfl) readonly.1
  have right := read_only_value (r := (i,1)) compatible (by rfl) readonly.2
  change c.choose i 9 = read64 p.initial (p.addr i p.rhs) at left
  change c.choose i 13 = read64 p.initial (p.addr i p.ap) at right
  have arith := (characterize p c i).1
  change decode (c.choose i 14) = decode (c.choose i 9) - decode (c.choose i 13) at arith
  exact arith.trans (by rw [left,right])

end PtxTorchLean.Poisson.PTX.Weak.Residual.Parallel

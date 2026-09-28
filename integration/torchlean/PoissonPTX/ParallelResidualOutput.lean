import PoissonPTX.ParallelResidual

namespace PtxTorchLean.Poisson.PTX.Weak.Residual.Parallel
open Kernel Sources

/-- Merge actual store records in any order. This models the observed storage
at completed launch publication; it is not a CUDA driver/host visibility proof. -/
def publish (p : Inputs n) (c : Candidate p) : List (Fin n) → Memory
  | [] => p.initial
  | i::rest => write64 (publish p c rest) (p.addr i p.output) (events p c (i,2)).value

/-- Distinct owners' byte ranges are disjoint, so store order cannot affect the
observed word. The caller need not choose a particular schedule. -/
theorem published_word (p : Inputs n) (c : Candidate p) (i : Fin n)
    (owners : ∀ i j, i≠j → Sources.Disjoint (p.addr i p.output) (p.addr j p.output))
    (order : List (Fin n)) (included : i∈order) :
    read64 (publish p c order) (p.addr i p.output) = (events p c (i,2)).value := by
  induction order with
  | nil => simp at included
  | cons j rest ih =>
    by_cases same : j=i
    · subst j; simp [publish]
    · rw [publish,read64_write64_disjoint _ _ _ _ (owners j i same)]
      apply ih
      exact (List.mem_cons.mp included).resolve_left (Ne.symm same)

/-- Whole output tensor correspondence after all owners' stores, for every
compatible candidate and every store order containing all active lanes. -/
theorem torchlean_output (p : Inputs n) (c : Candidate p)
    (source : (Fin n × Fin 3) → Fin 8 → Origin (Fin n × Fin 3))
    (compatible : Compatible p.initial (events p c) source)
    (separated : ∀ i j, Sources.Disjoint (p.addr j p.output) (p.addr i p.rhs) ∧
      Sources.Disjoint (p.addr j p.output) (p.addr i p.ap))
    (owners : ∀ i j, i≠j → Sources.Disjoint (p.addr i p.output) (p.addr j p.output))
    (order : List (Fin n)) (complete : ∀ i, i∈order) :
    Kernel.Residual.view (publish p c order) (fun i => p.addr i p.output) =
      TorchLean.Tensor.subSpec
        (Kernel.Residual.view p.initial (fun i => p.addr i p.rhs))
        (Kernel.Residual.view p.initial (fun i => p.addr i p.ap)) := by
  apply TorchLean.Tensor.Internal.Rep.ext
  intro coordinate
  rcases coordinate with ⟨i,unit⟩
  cases unit
  simp only [Kernel.Residual.view,TorchLean.Tensor.ofFn_apply,
    TorchLean.Tensor.subSpec,TorchLean.Tensor.map2Spec,TorchLean.Tensor.Internal.Rep.zipWith_apply]
  rw [published_word p c i owners order (complete i)]
  exact stored_value p c source compatible separated i

/-- Canonical choices give existence independently of the universal proof. -/
def canonical (p : Inputs n) (i : Fin n) (pc : Nat) : Word :=
  let a := read64 p.initial (p.addr i p.rhs)
  let b := read64 p.initial (p.addr i p.ap)
  if pc=9 then a else if pc=13 then b else encode (decode a-decode b)

def witness (p : Inputs n) : Candidate p where
  choose := canonical p
  final := fun i => finish (p.context i) (p.start i) p.count p.rhs p.ap p.output
    (canonical p i 9) (canonical p i 13) (canonical p i 14)
  trace := fun i => accesses (p.context i) (p.start i) p.count p.rhs p.ap p.output
    (canonical p i 9) (canonical p i 13) (canonical p i 14)
  run := by
    intro i
    rw [execution _ _ _ _ _ _ _ (p.pc i) (p.running i) (p.live i)
      (p.valid i p.rhs (by simp)) (p.valid i p.ap (by simp)) (p.valid i p.output (by simp))]
    simp [canonical,FP.Result,FP.apply]

/-- Actual successful instruction executions with a compatible initial source
for every read byte; not a claim of full PTX admission or GPU progress. -/
theorem witness_sources (p : Inputs n) :
    Compatible p.initial (events p (witness p)) (fun _ _ => .initial) := by
  intro e hr k
  rcases e with ⟨i,j⟩
  fin_cases j <;> simp_all [events,witness,canonical]

/-- Publication changes only actual output bytes; gaps and inputs remain intact. -/
theorem published_outside (p : Inputs n) (c : Candidate p) (order : List (Fin n)) (address : Nat)
    (outside : ∀ i, address < p.addr i p.output ∨ p.addr i p.output+8 ≤ address) :
    publish p c order address = p.initial address := by
  induction order with
  | nil => rfl
  | cons i rest ih =>
    rw [publish,write64_outside _ _ _ _ (outside i),ih]

end PtxTorchLean.Poisson.PTX.Weak.Residual.Parallel
